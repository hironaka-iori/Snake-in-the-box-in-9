import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-46, -48]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-50, -52])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1370)) (countLit q [-46, -48]) (countLit q [-50, -52]) (count1369 q) 1 1 (meaning1365 q) (meaning1367 q) (meaning1370 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1367 = false ∨ valuation q 1370 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true := by
  have hs : count1369 q = (countLit q [-46, -48]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-50, -52])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1371)) (countLit q [-46, -48]) (countLit q [-50, -52]) (count1369 q) 1 2 (meaning1365 q) (meaning1368 q) (meaning1371 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1368 = false ∨ valuation q 1371 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1370 = true := by
  have hs : count1369 q = (countLit q [-46, -48]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-50, -52])
  have hm := merge_left (literal (valuationOf q) (1366)) (literal (valuationOf q) (1370)) (countLit q [-46, -48]) (countLit q [-50, -52]) (count1369 q) 2 (meaning1366 q) (meaning1370 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1370 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1371 = true := by
  have hs : count1369 q = (countLit q [-46, -48]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-50, -52])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1371)) (countLit q [-46, -48]) (countLit q [-50, -52]) (count1369 q) 2 1 (meaning1366 q) (meaning1367 q) (meaning1371 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1367 = false ∨ valuation q 1371 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1372 = true := by
  have hs : count1369 q = (countLit q [-46, -48]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-50, -52])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1372)) (countLit q [-46, -48]) (countLit q [-50, -52]) (count1369 q) 2 2 (meaning1366 q) (meaning1368 q) (meaning1372 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1368 = false ∨ valuation q 1372 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-40, -42, -45]) + (countLit q [-46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -45]) (l₂ := [-46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1374)) (countLit q [-40, -42, -45]) (countLit q [-46, -48, -50, -52]) (count1373 q) 1 1 (meaning1362 q) (meaning1369 q) (meaning1374 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1369 = false ∨ valuation q 1374 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-40, -42, -45]) + (countLit q [-46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -45]) (l₂ := [-46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1375)) (countLit q [-40, -42, -45]) (countLit q [-46, -48, -50, -52]) (count1373 q) 1 2 (meaning1362 q) (meaning1370 q) (meaning1375 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1370 = false ∨ valuation q 1375 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1376 = true := by
  have hs : count1373 q = (countLit q [-40, -42, -45]) + (countLit q [-46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -45]) (l₂ := [-46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1371)) (literal (valuationOf q) (1376)) (countLit q [-40, -42, -45]) (countLit q [-46, -48, -50, -52]) (count1373 q) 1 3 (meaning1362 q) (meaning1371 q) (meaning1376 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1371 = false ∨ valuation q 1376 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 1362 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1377 = true := by
  have hs : count1373 q = (countLit q [-40, -42, -45]) + (countLit q [-46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -45]) (l₂ := [-46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1362)) (literal (valuationOf q) (1372)) (literal (valuationOf q) (1377)) (countLit q [-40, -42, -45]) (countLit q [-46, -48, -50, -52]) (count1373 q) 1 4 (meaning1362 q) (meaning1372 q) (meaning1377 q) hs
  change valuationOf q 1362 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 1362 = false ∨ valuation q 1372 = false ∨ valuation q 1377 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-40, -42, -45]) + (countLit q [-46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -45]) (l₂ := [-46, -48, -50, -52])
  have hm := merge_left (literal (valuationOf q) (1363)) (literal (valuationOf q) (1374)) (countLit q [-40, -42, -45]) (countLit q [-46, -48, -50, -52]) (count1373 q) 2 (meaning1363 q) (meaning1374 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1374 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-40, -42, -45]) + (countLit q [-46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -45]) (l₂ := [-46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1375)) (countLit q [-40, -42, -45]) (countLit q [-46, -48, -50, -52]) (count1373 q) 2 1 (meaning1363 q) (meaning1369 q) (meaning1375 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1369 = false ∨ valuation q 1375 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1376 = true := by
  have hs : count1373 q = (countLit q [-40, -42, -45]) + (countLit q [-46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -45]) (l₂ := [-46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1376)) (countLit q [-40, -42, -45]) (countLit q [-46, -48, -50, -52]) (count1373 q) 2 2 (meaning1363 q) (meaning1370 q) (meaning1376 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1370 = false ∨ valuation q 1376 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1377 = true := by
  have hs : count1373 q = (countLit q [-40, -42, -45]) + (countLit q [-46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -45]) (l₂ := [-46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1371)) (literal (valuationOf q) (1377)) (countLit q [-40, -42, -45]) (countLit q [-46, -48, -50, -52]) (count1373 q) 2 3 (meaning1363 q) (meaning1371 q) (meaning1377 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1371 = false ∨ valuation q 1377 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1378 = true := by
  have hs : count1373 q = (countLit q [-40, -42, -45]) + (countLit q [-46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -45]) (l₂ := [-46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1363)) (literal (valuationOf q) (1372)) (literal (valuationOf q) (1378)) (countLit q [-40, -42, -45]) (countLit q [-46, -48, -50, -52]) (count1373 q) 2 4 (meaning1363 q) (meaning1372 q) (meaning1378 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1372 = false ∨ valuation q 1378 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-40, -42, -45]) + (countLit q [-46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -45]) (l₂ := [-46, -48, -50, -52])
  have hm := merge_left (literal (valuationOf q) (1364)) (literal (valuationOf q) (1375)) (countLit q [-40, -42, -45]) (countLit q [-46, -48, -50, -52]) (count1373 q) 3 (meaning1364 q) (meaning1375 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1375 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1376 = true := by
  have hs : count1373 q = (countLit q [-40, -42, -45]) + (countLit q [-46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -45]) (l₂ := [-46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1376)) (countLit q [-40, -42, -45]) (countLit q [-46, -48, -50, -52]) (count1373 q) 3 1 (meaning1364 q) (meaning1369 q) (meaning1376 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1369 = false ∨ valuation q 1376 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1377 = true := by
  have hs : count1373 q = (countLit q [-40, -42, -45]) + (countLit q [-46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -45]) (l₂ := [-46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1364)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1377)) (countLit q [-40, -42, -45]) (countLit q [-46, -48, -50, -52]) (count1373 q) 3 2 (meaning1364 q) (meaning1370 q) (meaning1377 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1370 = false ∨ valuation q 1377 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1382 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1382)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 1 2 (meaning1353 q) (meaning1374 q) (meaning1382 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1374 = false ∨ valuation q 1382 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1383 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1383)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 1 3 (meaning1353 q) (meaning1375 q) (meaning1383 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1375 = false ∨ valuation q 1383 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1384 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1384)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 1 4 (meaning1353 q) (meaning1376 q) (meaning1384 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1376 = false ∨ valuation q 1384 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1385 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1377)) (literal (valuationOf q) (1385)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 1 5 (meaning1353 q) (meaning1377 q) (meaning1385 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1377 = false ∨ valuation q 1385 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1378 = false ∨ valuationOf q 1386 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1353)) (literal (valuationOf q) (1378)) (literal (valuationOf q) (1386)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 1 6 (meaning1353 q) (meaning1378 q) (meaning1386 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1378 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1378 = false ∨ valuation q 1386 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1383 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1383)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 2 2 (meaning1354 q) (meaning1374 q) (meaning1383 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1374 = false ∨ valuation q 1383 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1384 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1384)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 2 3 (meaning1354 q) (meaning1375 q) (meaning1384 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1375 = false ∨ valuation q 1384 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1385 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1385)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 2 4 (meaning1354 q) (meaning1376 q) (meaning1385 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1376 = false ∨ valuation q 1385 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1386 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1354)) (literal (valuationOf q) (1377)) (literal (valuationOf q) (1386)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 2 5 (meaning1354 q) (meaning1377 q) (meaning1386 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1377 = false ∨ valuation q 1386 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1384 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1384)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 3 2 (meaning1355 q) (meaning1374 q) (meaning1384 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1374 = false ∨ valuation q 1384 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1385 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1385)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 3 3 (meaning1355 q) (meaning1375 q) (meaning1385 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1375 = false ∨ valuation q 1385 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 1355 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1386 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1355)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1386)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 3 4 (meaning1355 q) (meaning1376 q) (meaning1386 q) hs
  change valuationOf q 1355 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 1355 = false ∨ valuation q 1376 = false ∨ valuation q 1386 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1386 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1356)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1386)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 4 3 (meaning1356 q) (meaning1375 q) (meaning1386 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1375 = false ∨ valuation q 1386 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1387 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1356)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1387)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 4 4 (meaning1356 q) (meaning1376 q) (meaning1387 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1376 = false ∨ valuation q 1387 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1386 = true := by
  have hs : count1380 q = (countLit q [-27, -29, -31, -33, -35, -36, -39]) + (countLit q [-40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -33, -35, -36, -39]) (l₂ := [-40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1386)) (countLit q [-27, -29, -31, -33, -35, -36, -39]) (countLit q [-40, -42, -45, -46, -48, -50, -52]) (count1380 q) 5 2 (meaning1357 q) (meaning1374 q) (meaning1386 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1374 = false ∨ valuation q 1386 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E090.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112090
