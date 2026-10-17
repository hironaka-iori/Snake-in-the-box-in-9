import E112225Semantics
import B112E225Inputs
namespace Snake9.Regrowth.E112225
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 1295 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1322 = true := by
  have hs : count1319 q = (countLit q [-27, -29, -31, -33, -34, -36]) + (countLit q [-39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -34, -36]) (l₂ := [-39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1295)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1322)) (countLit q [-27, -29, -31, -33, -34, -36]) (countLit q [-39, -40, -43, -45, -47, -49, -50]) (count1319 q) 3 1 (meaning1295 q) (meaning1312 q) (meaning1322 q) hs
  change valuationOf q 1295 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 1295 = false ∨ valuation q 1312 = false ∨ valuation q 1322 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 1295 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1323 = true := by
  have hs : count1319 q = (countLit q [-27, -29, -31, -33, -34, -36]) + (countLit q [-39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -34, -36]) (l₂ := [-39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1295)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1323)) (countLit q [-27, -29, -31, -33, -34, -36]) (countLit q [-39, -40, -43, -45, -47, -49, -50]) (count1319 q) 3 2 (meaning1295 q) (meaning1313 q) (meaning1323 q) hs
  change valuationOf q 1295 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 1295 = false ∨ valuation q 1313 = false ∨ valuation q 1323 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1331 = true := by
  have hs : count1329 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) + (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (l₂ := [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1331)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (count1329 q) 1 2 (meaning1273 q) (meaning1320 q) (meaning1331 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1320 = false ∨ valuation q 1331 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1332 = true := by
  have hs : count1329 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) + (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (l₂ := [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1332)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (count1329 q) 1 3 (meaning1273 q) (meaning1321 q) (meaning1332 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1321 = false ∨ valuation q 1332 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1333 = true := by
  have hs : count1329 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) + (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (l₂ := [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1333)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (count1329 q) 1 4 (meaning1273 q) (meaning1322 q) (meaning1333 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1322 = false ∨ valuation q 1333 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1331 = true := by
  have hs : count1329 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) + (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (l₂ := [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1331)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (count1329 q) 2 1 (meaning1274 q) (meaning1319 q) (meaning1331 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1319 = false ∨ valuation q 1331 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1332 = true := by
  have hs : count1329 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) + (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (l₂ := [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1332)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (count1329 q) 2 2 (meaning1274 q) (meaning1320 q) (meaning1332 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1320 = false ∨ valuation q 1332 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1333 = true := by
  have hs : count1329 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) + (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (l₂ := [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1333)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (count1329 q) 2 3 (meaning1274 q) (meaning1321 q) (meaning1333 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1321 = false ∨ valuation q 1333 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1334 = true := by
  have hs : count1329 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) + (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (l₂ := [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1334)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (count1329 q) 2 4 (meaning1274 q) (meaning1322 q) (meaning1334 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1322 = false ∨ valuation q 1334 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 1274 = false ∨ valuationOf q 1323 = false ∨ valuationOf q 1335 = true := by
  have hs : count1329 q = (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) + (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (l₂ := [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50])
  have hm := merge_two (literal (valuationOf q) (1274)) (literal (valuationOf q) (1323)) (literal (valuationOf q) (1335)) (countLit q [-2, -4, -7, -8, -11, -13, -15, -17, -18, -20, -23, -24]) (countLit q [-27, -29, -31, -33, -34, -36, -39, -40, -43, -45, -47, -49, -50]) (count1329 q) 2 5 (meaning1274 q) (meaning1323 q) (meaning1335 q) hs
  change valuationOf q 1274 = false ∨ valuationOf q 1323 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 1274 = false ∨ valuation q 1323 = false ∨ valuation q 1335 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1339 = true := by
  have hs : count1339 q = (countLit q [-55]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1339)) (countLit q [-55]) (countLit q [-58]) (count1339 q) 1 (meaningNeg58 q) (meaning1339 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1339 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-52]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-55, -58])
  have hm := merge_right (literal (valuationOf q) (1339)) (literal (valuationOf q) (1341)) (countLit q [-52]) (countLit q [-55, -58]) (count1341 q) 1 (meaning1339 q) (meaning1341 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1341 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1341 = true := by
  have hs : count1341 q = (countLit q [-52]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-55, -58])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1341)) (countLit q [-52]) (countLit q [-55, -58]) (count1341 q) 1 (meaningNeg52 q) (meaning1341 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1341 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1344 = true := by
  have hs : count1344 q = (countLit q [-61]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (1344)) (countLit q [-61]) (countLit q [-64]) (count1344 q) 1 (meaningNeg64 q) (meaning1344 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1344 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1346 = true := by
  have hs : count1346 q = (countLit q [-59]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -64])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1346)) (countLit q [-59]) (countLit q [-61, -64]) (count1346 q) 1 (meaningNeg59 q) (meaning1346 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1346 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1344 = false ∨ valuationOf q 1347 = true := by
  have hs : count1346 q = (countLit q [-59]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -64])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1347)) (countLit q [-59]) (countLit q [-61, -64]) (count1346 q) 1 1 (meaningNeg59 q) (meaning1344 q) (meaning1347 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1344 = false ∨ valuation q 1347 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-52, -55, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_right (literal (valuationOf q) (1346)) (literal (valuationOf q) (1349)) (countLit q [-52, -55, -58]) (countLit q [-59, -61, -64]) (count1349 q) 1 (meaning1346 q) (meaning1349 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1349 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 1347 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-52, -55, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_right (literal (valuationOf q) (1347)) (literal (valuationOf q) (1350)) (countLit q [-52, -55, -58]) (countLit q [-59, -61, -64]) (count1349 q) 2 (meaning1347 q) (meaning1350 q) hs
  change valuationOf q 1347 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 1347 = false ∨ valuation q 1350 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-52, -55, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_left (literal (valuationOf q) (1341)) (literal (valuationOf q) (1349)) (countLit q [-52, -55, -58]) (countLit q [-59, -61, -64]) (count1349 q) 1 (meaning1341 q) (meaning1349 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1349 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-52, -55, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-52, -55, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_two (literal (valuationOf q) (1341)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1350)) (countLit q [-52, -55, -58]) (countLit q [-59, -61, -64]) (count1349 q) 1 1 (meaning1341 q) (meaning1346 q) (meaning1350 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1346 = false ∨ valuation q 1350 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1355 = true := by
  have hs : count1355 q = (countLit q [-68]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1355)) (countLit q [-68]) (countLit q [-70]) (count1355 q) 1 (meaningNeg70 q) (meaning1355 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1355 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1355 = true := by
  have hs : count1355 q = (countLit q [-68]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1355)) (countLit q [-68]) (countLit q [-70]) (count1355 q) 1 (meaningNeg68 q) (meaning1355 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1355 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1357 = true := by
  have hs : count1357 q = (countLit q [-66]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68, -70])
  have hm := merge_right (literal (valuationOf q) (1355)) (literal (valuationOf q) (1357)) (countLit q [-66]) (countLit q [-68, -70]) (count1357 q) 1 (meaning1355 q) (meaning1357 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1357 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1360 = true := by
  have hs : count1360 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1360)) (countLit q [-74]) (countLit q [-76]) (count1360 q) 1 (meaningNeg76 q) (meaning1360 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1360 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1360 = true := by
  have hs : count1360 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1360)) (countLit q [-74]) (countLit q [-76]) (count1360 q) 1 (meaningNeg74 q) (meaning1360 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1360 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1361 = true := by
  have hs : count1360 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1361)) (countLit q [-74]) (countLit q [-76]) (count1360 q) 1 1 (meaningNeg74 q) (meaningNeg76 q) (meaning1361 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 1361 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-73]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74, -76])
  have hm := merge_right (literal (valuationOf q) (1360)) (literal (valuationOf q) (1362)) (countLit q [-73]) (countLit q [-74, -76]) (count1362 q) 1 (meaning1360 q) (meaning1362 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1362 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-73]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74, -76])
  have hm := merge_right (literal (valuationOf q) (1361)) (literal (valuationOf q) (1363)) (countLit q [-73]) (countLit q [-74, -76]) (count1362 q) 2 (meaning1361 q) (meaning1363 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1363 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1362 = true := by
  have hs : count1362 q = (countLit q [-73]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74, -76])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1362)) (countLit q [-73]) (countLit q [-74, -76]) (count1362 q) 1 (meaningNeg73 q) (meaning1362 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1362 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1360 = false ∨ valuationOf q 1363 = true := by
  have hs : count1362 q = (countLit q [-73]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74, -76])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (1360)) (literal (valuationOf q) (1363)) (countLit q [-73]) (countLit q [-74, -76]) (count1362 q) 1 1 (meaningNeg73 q) (meaning1360 q) (meaning1363 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1360 = false ∨ valuation q 1363 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1365 = true := by
  have hs : count1365 q = (countLit q [-66, -68, -70]) + (countLit q [-73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-66, -68, -70]) (l₂ := [-73, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1362)) (literal (valuationOf q) (1365)) (countLit q [-66, -68, -70]) (countLit q [-73, -74, -76]) (count1365 q) 1 (meaning1362 q) (meaning1365 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1365 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1366 = true := by
  have hs : count1365 q = (countLit q [-66, -68, -70]) + (countLit q [-73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-66, -68, -70]) (l₂ := [-73, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1363)) (literal (valuationOf q) (1366)) (countLit q [-66, -68, -70]) (countLit q [-73, -74, -76]) (count1365 q) 2 (meaning1363 q) (meaning1366 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1366 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E225.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112225
