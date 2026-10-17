import E112190Semantics
import B112E190Inputs
namespace Snake9.Regrowth.E112190
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1362 = true := by
  have hs : count1361 q = (countLit q [-51]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1362)) (countLit q [-51]) (countLit q [-54]) (count1361 q) 1 1 (meaningNeg51 q) (meaningNeg54 q) (meaning1362 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 54 = true ∨ valuation q 1362 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 1361 = false ∨ valuationOf q 1363 = true := by
  have hs : count1363 q = (countLit q [-48, -49]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-51, -54])
  have hm := merge_right (literal (valuationOf q) (1361)) (literal (valuationOf q) (1363)) (countLit q [-48, -49]) (countLit q [-51, -54]) (count1363 q) 1 (meaning1361 q) (meaning1363 q) hs
  change valuationOf q 1361 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 1361 = false ∨ valuation q 1363 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1363 = true := by
  have hs : count1363 q = (countLit q [-48, -49]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-51, -54])
  have hm := merge_left (literal (valuationOf q) (1359)) (literal (valuationOf q) (1363)) (countLit q [-48, -49]) (countLit q [-51, -54]) (count1363 q) 1 (meaning1359 q) (meaning1363 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1363 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1361 = false ∨ valuationOf q 1364 = true := by
  have hs : count1363 q = (countLit q [-48, -49]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-51, -54])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1361)) (literal (valuationOf q) (1364)) (countLit q [-48, -49]) (countLit q [-51, -54]) (count1363 q) 1 1 (meaning1359 q) (meaning1361 q) (meaning1364 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1361 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1361 = false ∨ valuation q 1364 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 1359 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1365 = true := by
  have hs : count1363 q = (countLit q [-48, -49]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-51, -54])
  have hm := merge_two (literal (valuationOf q) (1359)) (literal (valuationOf q) (1362)) (literal (valuationOf q) (1365)) (countLit q [-48, -49]) (countLit q [-51, -54]) (count1363 q) 1 2 (meaning1359 q) (meaning1362 q) (meaning1365 q) hs
  change valuationOf q 1359 = false ∨ valuationOf q 1362 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 1359 = false ∨ valuation q 1362 = false ∨ valuation q 1365 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1364 = true := by
  have hs : count1363 q = (countLit q [-48, -49]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-51, -54])
  have hm := merge_left (literal (valuationOf q) (1360)) (literal (valuationOf q) (1364)) (countLit q [-48, -49]) (countLit q [-51, -54]) (count1363 q) 2 (meaning1360 q) (meaning1364 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1364 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1361 = false ∨ valuationOf q 1365 = true := by
  have hs : count1363 q = (countLit q [-48, -49]) + (countLit q [-51, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-51, -54])
  have hm := merge_two (literal (valuationOf q) (1360)) (literal (valuationOf q) (1361)) (literal (valuationOf q) (1365)) (countLit q [-48, -49]) (countLit q [-51, -54]) (count1363 q) 2 1 (meaning1360 q) (meaning1361 q) (meaning1365 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1361 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1361 = false ∨ valuation q 1365 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 1363 = false ∨ valuationOf q 1367 = true := by
  have hs : count1367 q = (countLit q [-41, -43, -46]) + (countLit q [-48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-48, -49, -51, -54])
  have hm := merge_right (literal (valuationOf q) (1363)) (literal (valuationOf q) (1367)) (countLit q [-41, -43, -46]) (countLit q [-48, -49, -51, -54]) (count1367 q) 1 (meaning1363 q) (meaning1367 q) hs
  change valuationOf q 1363 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 1363 = false ∨ valuation q 1367 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 1364 = false ∨ valuationOf q 1368 = true := by
  have hs : count1367 q = (countLit q [-41, -43, -46]) + (countLit q [-48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-48, -49, -51, -54])
  have hm := merge_right (literal (valuationOf q) (1364)) (literal (valuationOf q) (1368)) (countLit q [-41, -43, -46]) (countLit q [-48, -49, -51, -54]) (count1367 q) 2 (meaning1364 q) (meaning1368 q) hs
  change valuationOf q 1364 = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 1364 = false ∨ valuation q 1368 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1369 = true := by
  have hs : count1367 q = (countLit q [-41, -43, -46]) + (countLit q [-48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-48, -49, -51, -54])
  have hm := merge_right (literal (valuationOf q) (1365)) (literal (valuationOf q) (1369)) (countLit q [-41, -43, -46]) (countLit q [-48, -49, -51, -54]) (count1367 q) 3 (meaning1365 q) (meaning1369 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1369 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1368 = true := by
  have hs : count1367 q = (countLit q [-41, -43, -46]) + (countLit q [-48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1356)) (literal (valuationOf q) (1363)) (literal (valuationOf q) (1368)) (countLit q [-41, -43, -46]) (countLit q [-48, -49, -51, -54]) (count1367 q) 1 1 (meaning1356 q) (meaning1363 q) (meaning1368 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1363 = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1363 = false ∨ valuation q 1368 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1369 = true := by
  have hs : count1367 q = (countLit q [-41, -43, -46]) + (countLit q [-48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1356)) (literal (valuationOf q) (1364)) (literal (valuationOf q) (1369)) (countLit q [-41, -43, -46]) (countLit q [-48, -49, -51, -54]) (count1367 q) 1 2 (meaning1356 q) (meaning1364 q) (meaning1369 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1364 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1364 = false ∨ valuation q 1369 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1370 = true := by
  have hs : count1367 q = (countLit q [-41, -43, -46]) + (countLit q [-48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1356)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1370)) (countLit q [-41, -43, -46]) (countLit q [-48, -49, -51, -54]) (count1367 q) 1 3 (meaning1356 q) (meaning1365 q) (meaning1370 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1365 = false ∨ valuation q 1370 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1371 = true := by
  have hs : count1367 q = (countLit q [-41, -43, -46]) + (countLit q [-48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -46]) (l₂ := [-48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1371)) (countLit q [-41, -43, -46]) (countLit q [-48, -49, -51, -54]) (count1367 q) 2 3 (meaning1357 q) (meaning1365 q) (meaning1371 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1365 = false ∨ valuation q 1371 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1375 = true := by
  have hs : count1374 q = (countLit q [-30, -32, -33, -35, -38, -40]) + (countLit q [-41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -38, -40]) (l₂ := [-41, -43, -46, -48, -49, -51, -54])
  have hm := merge_right (literal (valuationOf q) (1368)) (literal (valuationOf q) (1375)) (countLit q [-30, -32, -33, -35, -38, -40]) (countLit q [-41, -43, -46, -48, -49, -51, -54]) (count1374 q) 2 (meaning1368 q) (meaning1375 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1375 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1375 = true := by
  have hs : count1374 q = (countLit q [-30, -32, -33, -35, -38, -40]) + (countLit q [-41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -38, -40]) (l₂ := [-41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1348)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1375)) (countLit q [-30, -32, -33, -35, -38, -40]) (countLit q [-41, -43, -46, -48, -49, -51, -54]) (count1374 q) 1 1 (meaning1348 q) (meaning1367 q) (meaning1375 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1367 = false ∨ valuation q 1375 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1376 = true := by
  have hs : count1374 q = (countLit q [-30, -32, -33, -35, -38, -40]) + (countLit q [-41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -38, -40]) (l₂ := [-41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1348)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1376)) (countLit q [-30, -32, -33, -35, -38, -40]) (countLit q [-41, -43, -46, -48, -49, -51, -54]) (count1374 q) 1 2 (meaning1348 q) (meaning1368 q) (meaning1376 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1368 = false ∨ valuation q 1376 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1377 = true := by
  have hs : count1374 q = (countLit q [-30, -32, -33, -35, -38, -40]) + (countLit q [-41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -38, -40]) (l₂ := [-41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1348)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1377)) (countLit q [-30, -32, -33, -35, -38, -40]) (countLit q [-41, -43, -46, -48, -49, -51, -54]) (count1374 q) 1 3 (meaning1348 q) (meaning1369 q) (meaning1377 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1369 = false ∨ valuation q 1377 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1378 = true := by
  have hs : count1374 q = (countLit q [-30, -32, -33, -35, -38, -40]) + (countLit q [-41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -38, -40]) (l₂ := [-41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1348)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1378)) (countLit q [-30, -32, -33, -35, -38, -40]) (countLit q [-41, -43, -46, -48, -49, -51, -54]) (count1374 q) 1 4 (meaning1348 q) (meaning1370 q) (meaning1378 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1370 = false ∨ valuation q 1378 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1379 = true := by
  have hs : count1374 q = (countLit q [-30, -32, -33, -35, -38, -40]) + (countLit q [-41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -38, -40]) (l₂ := [-41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1348)) (literal (valuationOf q) (1371)) (literal (valuationOf q) (1379)) (countLit q [-30, -32, -33, -35, -38, -40]) (countLit q [-41, -43, -46, -48, -49, -51, -54]) (count1374 q) 1 5 (meaning1348 q) (meaning1371 q) (meaning1379 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1371 = false ∨ valuation q 1379 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1376 = true := by
  have hs : count1374 q = (countLit q [-30, -32, -33, -35, -38, -40]) + (countLit q [-41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -38, -40]) (l₂ := [-41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1367)) (literal (valuationOf q) (1376)) (countLit q [-30, -32, -33, -35, -38, -40]) (countLit q [-41, -43, -46, -48, -49, -51, -54]) (count1374 q) 2 1 (meaning1349 q) (meaning1367 q) (meaning1376 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1367 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1367 = false ∨ valuation q 1376 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1377 = true := by
  have hs : count1374 q = (countLit q [-30, -32, -33, -35, -38, -40]) + (countLit q [-41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -38, -40]) (l₂ := [-41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1377)) (countLit q [-30, -32, -33, -35, -38, -40]) (countLit q [-41, -43, -46, -48, -49, -51, -54]) (count1374 q) 2 2 (meaning1349 q) (meaning1368 q) (meaning1377 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1368 = false ∨ valuation q 1377 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1378 = true := by
  have hs : count1374 q = (countLit q [-30, -32, -33, -35, -38, -40]) + (countLit q [-41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -38, -40]) (l₂ := [-41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1369)) (literal (valuationOf q) (1378)) (countLit q [-30, -32, -33, -35, -38, -40]) (countLit q [-41, -43, -46, -48, -49, -51, -54]) (count1374 q) 2 3 (meaning1349 q) (meaning1369 q) (meaning1378 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1369 = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1369 = false ∨ valuation q 1378 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1391 = true := by
  have hs : count1387 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) + (countLit q [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) (l₂ := [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1391)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) (countLit q [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (count1387 q) 3 2 (meaning1327 q) (meaning1375 q) (meaning1391 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1375 = false ∨ valuation q 1391 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1392 = true := by
  have hs : count1387 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) + (countLit q [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) (l₂ := [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1392)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) (countLit q [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (count1387 q) 3 3 (meaning1327 q) (meaning1376 q) (meaning1392 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1376 = false ∨ valuation q 1392 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1393 = true := by
  have hs : count1387 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) + (countLit q [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) (l₂ := [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1377)) (literal (valuationOf q) (1393)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) (countLit q [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (count1387 q) 3 4 (meaning1327 q) (meaning1377 q) (meaning1393 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1377 = false ∨ valuation q 1393 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1378 = false ∨ valuationOf q 1394 = true := by
  have hs : count1387 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) + (countLit q [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) (l₂ := [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1378)) (literal (valuationOf q) (1394)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) (countLit q [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (count1387 q) 3 5 (meaning1327 q) (meaning1378 q) (meaning1394 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1378 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1378 = false ∨ valuation q 1394 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1395 = true := by
  have hs : count1387 q = (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) + (countLit q [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) (l₂ := [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1395)) (countLit q [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]) (countLit q [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]) (count1387 q) 3 6 (meaning1327 q) (meaning1379 q) (meaning1395 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1379 = false ∨ valuation q 1395 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1400 = true := by
  have hs : count1400 q = (countLit q [-57]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (1400)) (countLit q [-57]) (countLit q [-59]) (count1400 q) 1 (meaningNeg59 q) (meaning1400 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1400 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-56]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57, -59])
  have hm := merge_right (literal (valuationOf q) (1400)) (literal (valuationOf q) (1402)) (countLit q [-56]) (countLit q [-57, -59]) (count1402 q) 1 (meaning1400 q) (meaning1402 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1402 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-56]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57, -59])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1402)) (countLit q [-56]) (countLit q [-57, -59]) (count1402 q) 1 (meaningNeg56 q) (meaning1402 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1402 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1405 = true := by
  have hs : count1405 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_right (literal (valuationOf q) (-65)) (literal (valuationOf q) (1405)) (countLit q [-64]) (countLit q [-65]) (count1405 q) 1 (meaningNeg65 q) (meaning1405 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1405 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E190.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112190
