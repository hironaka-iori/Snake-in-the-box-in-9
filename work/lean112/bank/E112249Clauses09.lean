import E112249Semantics
import B112E249Inputs
namespace Snake9.Regrowth.E112249
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 1347 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-50]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51, -52])
  have hm := merge_right (literal (valuationOf q) (1347)) (literal (valuationOf q) (1349)) (countLit q [-50]) (countLit q [-51, -52]) (count1349 q) 1 (meaning1347 q) (meaning1349 q) hs
  change valuationOf q 1347 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 1347 = false ∨ valuation q 1349 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-50]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51, -52])
  have hm := merge_right (literal (valuationOf q) (1348)) (literal (valuationOf q) (1350)) (countLit q [-50]) (countLit q [-51, -52]) (count1349 q) 2 (meaning1348 q) (meaning1350 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1350 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-50]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51, -52])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1349)) (countLit q [-50]) (countLit q [-51, -52]) (count1349 q) 1 (meaningNeg50 q) (meaning1349 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1349 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1347 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-50]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (1347)) (literal (valuationOf q) (1350)) (countLit q [-50]) (countLit q [-51, -52]) (count1349 q) 1 1 (meaningNeg50 q) (meaning1347 q) (meaning1350 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1347 = false ∨ valuation q 1350 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1352 = true := by
  have hs : count1352 q = (countLit q [-41, -42, -48]) + (countLit q [-50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -48]) (l₂ := [-50, -51, -52])
  have hm := merge_right (literal (valuationOf q) (1349)) (literal (valuationOf q) (1352)) (countLit q [-41, -42, -48]) (countLit q [-50, -51, -52]) (count1352 q) 1 (meaning1349 q) (meaning1352 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1352 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1352 = true := by
  have hs : count1352 q = (countLit q [-41, -42, -48]) + (countLit q [-50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -48]) (l₂ := [-50, -51, -52])
  have hm := merge_left (literal (valuationOf q) (1344)) (literal (valuationOf q) (1352)) (countLit q [-41, -42, -48]) (countLit q [-50, -51, -52]) (count1352 q) 1 (meaning1344 q) (meaning1352 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1352 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1353 = true := by
  have hs : count1352 q = (countLit q [-41, -42, -48]) + (countLit q [-50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -48]) (l₂ := [-50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1353)) (countLit q [-41, -42, -48]) (countLit q [-50, -51, -52]) (count1352 q) 1 1 (meaning1344 q) (meaning1349 q) (meaning1353 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1349 = false ∨ valuation q 1353 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1354 = true := by
  have hs : count1352 q = (countLit q [-41, -42, -48]) + (countLit q [-50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -48]) (l₂ := [-50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1344)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1354)) (countLit q [-41, -42, -48]) (countLit q [-50, -51, -52]) (count1352 q) 1 2 (meaning1344 q) (meaning1350 q) (meaning1354 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1350 = false ∨ valuation q 1354 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1353 = true := by
  have hs : count1352 q = (countLit q [-41, -42, -48]) + (countLit q [-50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -48]) (l₂ := [-50, -51, -52])
  have hm := merge_left (literal (valuationOf q) (1345)) (literal (valuationOf q) (1353)) (countLit q [-41, -42, -48]) (countLit q [-50, -51, -52]) (count1352 q) 2 (meaning1345 q) (meaning1353 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1353 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1354 = true := by
  have hs : count1352 q = (countLit q [-41, -42, -48]) + (countLit q [-50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -48]) (l₂ := [-50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1354)) (countLit q [-41, -42, -48]) (countLit q [-50, -51, -52]) (count1352 q) 2 1 (meaning1345 q) (meaning1349 q) (meaning1354 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1349 = false ∨ valuation q 1354 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1354 = true := by
  have hs : count1352 q = (countLit q [-41, -42, -48]) + (countLit q [-50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -48]) (l₂ := [-50, -51, -52])
  have hm := merge_left (literal (valuationOf q) (1346)) (literal (valuationOf q) (1354)) (countLit q [-41, -42, -48]) (countLit q [-50, -51, -52]) (count1352 q) 3 (meaning1346 q) (meaning1354 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1354 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-28, -29, -30, -34, -38, -40]) + (countLit q [-41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -34, -38, -40]) (l₂ := [-41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1336)) (literal (valuationOf q) (1352)) (literal (valuationOf q) (1359)) (countLit q [-28, -29, -30, -34, -38, -40]) (countLit q [-41, -42, -48, -50, -51, -52]) (count1358 q) 1 1 (meaning1336 q) (meaning1352 q) (meaning1359 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1352 = false ∨ valuation q 1359 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1360 = true := by
  have hs : count1358 q = (countLit q [-28, -29, -30, -34, -38, -40]) + (countLit q [-41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -34, -38, -40]) (l₂ := [-41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1336)) (literal (valuationOf q) (1353)) (literal (valuationOf q) (1360)) (countLit q [-28, -29, -30, -34, -38, -40]) (countLit q [-41, -42, -48, -50, -51, -52]) (count1358 q) 1 2 (meaning1336 q) (meaning1353 q) (meaning1360 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1353 = false ∨ valuation q 1360 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 1336 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1361 = true := by
  have hs : count1358 q = (countLit q [-28, -29, -30, -34, -38, -40]) + (countLit q [-41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -34, -38, -40]) (l₂ := [-41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1336)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1361)) (countLit q [-28, -29, -30, -34, -38, -40]) (countLit q [-41, -42, -48, -50, -51, -52]) (count1358 q) 1 3 (meaning1336 q) (meaning1354 q) (meaning1361 q) hs
  change valuationOf q 1336 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 1336 = false ∨ valuation q 1354 = false ∨ valuation q 1361 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-28, -29, -30, -34, -38, -40]) + (countLit q [-41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -34, -38, -40]) (l₂ := [-41, -42, -48, -50, -51, -52])
  have hm := merge_left (literal (valuationOf q) (1337)) (literal (valuationOf q) (1359)) (countLit q [-28, -29, -30, -34, -38, -40]) (countLit q [-41, -42, -48, -50, -51, -52]) (count1358 q) 2 (meaning1337 q) (meaning1359 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1359 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1360 = true := by
  have hs : count1358 q = (countLit q [-28, -29, -30, -34, -38, -40]) + (countLit q [-41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -34, -38, -40]) (l₂ := [-41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1337)) (literal (valuationOf q) (1352)) (literal (valuationOf q) (1360)) (countLit q [-28, -29, -30, -34, -38, -40]) (countLit q [-41, -42, -48, -50, -51, -52]) (count1358 q) 2 1 (meaning1337 q) (meaning1352 q) (meaning1360 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1352 = false ∨ valuation q 1360 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 1337 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1361 = true := by
  have hs : count1358 q = (countLit q [-28, -29, -30, -34, -38, -40]) + (countLit q [-41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -34, -38, -40]) (l₂ := [-41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1337)) (literal (valuationOf q) (1353)) (literal (valuationOf q) (1361)) (countLit q [-28, -29, -30, -34, -38, -40]) (countLit q [-41, -42, -48, -50, -51, -52]) (count1358 q) 2 2 (meaning1337 q) (meaning1353 q) (meaning1361 q) hs
  change valuationOf q 1337 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 1337 = false ∨ valuation q 1353 = false ∨ valuation q 1361 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1361 = true := by
  have hs : count1358 q = (countLit q [-28, -29, -30, -34, -38, -40]) + (countLit q [-41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -34, -38, -40]) (l₂ := [-41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1338)) (literal (valuationOf q) (1352)) (literal (valuationOf q) (1361)) (countLit q [-28, -29, -30, -34, -38, -40]) (countLit q [-41, -42, -48, -50, -51, -52]) (count1358 q) 3 1 (meaning1338 q) (meaning1352 q) (meaning1361 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1352 = false ∨ valuation q 1361 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1362 = true := by
  have hs : count1358 q = (countLit q [-28, -29, -30, -34, -38, -40]) + (countLit q [-41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -34, -38, -40]) (l₂ := [-41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1338)) (literal (valuationOf q) (1353)) (literal (valuationOf q) (1362)) (countLit q [-28, -29, -30, -34, -38, -40]) (countLit q [-41, -42, -48, -50, -51, -52]) (count1358 q) 3 2 (meaning1338 q) (meaning1353 q) (meaning1362 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1353 = false ∨ valuation q 1362 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1369 = true := by
  have hs : count1367 q = (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) + (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (l₂ := [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1317)) (literal (valuationOf q) (1359)) (literal (valuationOf q) (1369)) (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (count1367 q) 1 2 (meaning1317 q) (meaning1359 q) (meaning1369 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1359 = false ∨ valuation q 1369 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1370 = true := by
  have hs : count1367 q = (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) + (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (l₂ := [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1317)) (literal (valuationOf q) (1360)) (literal (valuationOf q) (1370)) (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (count1367 q) 1 3 (meaning1317 q) (meaning1360 q) (meaning1370 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1360 = false ∨ valuation q 1370 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1361 = false ∨ valuationOf q 1371 = true := by
  have hs : count1367 q = (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) + (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (l₂ := [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1317)) (literal (valuationOf q) (1361)) (literal (valuationOf q) (1371)) (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (count1367 q) 1 4 (meaning1317 q) (meaning1361 q) (meaning1371 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1361 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1361 = false ∨ valuation q 1371 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1372 = true := by
  have hs : count1367 q = (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) + (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (l₂ := [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1317)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1372)) (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (count1367 q) 1 5 (meaning1317 q) (meaning1362 q) (meaning1372 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1362 = false ∨ valuation q 1372 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 1318 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1370 = true := by
  have hs : count1367 q = (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) + (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (l₂ := [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1318)) (literal (valuationOf q) (1359)) (literal (valuationOf q) (1370)) (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (count1367 q) 2 2 (meaning1318 q) (meaning1359 q) (meaning1370 q) hs
  change valuationOf q 1318 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 1318 = false ∨ valuation q 1359 = false ∨ valuation q 1370 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 1318 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1371 = true := by
  have hs : count1367 q = (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) + (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (l₂ := [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1318)) (literal (valuationOf q) (1360)) (literal (valuationOf q) (1371)) (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (count1367 q) 2 3 (meaning1318 q) (meaning1360 q) (meaning1371 q) hs
  change valuationOf q 1318 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 1318 = false ∨ valuation q 1360 = false ∨ valuation q 1371 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 1318 = false ∨ valuationOf q 1361 = false ∨ valuationOf q 1372 = true := by
  have hs : count1367 q = (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) + (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (l₂ := [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1318)) (literal (valuationOf q) (1361)) (literal (valuationOf q) (1372)) (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (count1367 q) 2 4 (meaning1318 q) (meaning1361 q) (meaning1372 q) hs
  change valuationOf q 1318 = false ∨ valuationOf q 1361 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 1318 = false ∨ valuation q 1361 = false ∨ valuation q 1372 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1372 = true := by
  have hs : count1367 q = (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) + (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (l₂ := [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1360)) (literal (valuationOf q) (1372)) (countLit q [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]) (countLit q [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]) (count1367 q) 3 3 (meaning1319 q) (meaning1360 q) (meaning1372 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1360 = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1360 = false ∨ valuation q 1372 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1376 = true := by
  have hs : count1376 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (1376)) (countLit q [-56]) (countLit q [-59]) (count1376 q) 1 (meaningNeg59 q) (meaning1376 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1376 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1376 = true := by
  have hs : count1376 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1376)) (countLit q [-56]) (countLit q [-59]) (count1376 q) 1 (meaningNeg56 q) (meaning1376 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1376 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1378 = true := by
  have hs : count1378 q = (countLit q [-54]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -59])
  have hm := merge_right (literal (valuationOf q) (1376)) (literal (valuationOf q) (1378)) (countLit q [-54]) (countLit q [-56, -59]) (count1378 q) 1 (meaning1376 q) (meaning1378 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1378 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1378 = true := by
  have hs : count1378 q = (countLit q [-54]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -59])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1378)) (countLit q [-54]) (countLit q [-56, -59]) (count1378 q) 1 (meaningNeg54 q) (meaning1378 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1378 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1376 = false ∨ valuationOf q 1379 = true := by
  have hs : count1378 q = (countLit q [-54]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -59])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1379)) (countLit q [-54]) (countLit q [-56, -59]) (count1378 q) 1 1 (meaningNeg54 q) (meaning1376 q) (meaning1379 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1376 = false ∨ valuation q 1379 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E249.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112249
