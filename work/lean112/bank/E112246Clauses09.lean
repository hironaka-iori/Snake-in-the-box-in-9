import E112246Semantics
import B112E246Inputs
namespace Snake9.Regrowth.E112246
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1395 = false ∨ valuationOf q 1403 = true := by
  have hs : count1399 q = (countLit q [-54, -55, -57, -60, -61, -64]) + (countLit q [-65, -67, -70, -71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64]) (l₂ := [-65, -67, -70, -71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1395)) (literal (valuationOf q) (1403)) (countLit q [-54, -55, -57, -60, -61, -64]) (countLit q [-65, -67, -70, -71, -73, -76, -79]) (count1399 q) 1 4 (meaning1373 q) (meaning1395 q) (meaning1403 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1395 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1395 = false ∨ valuation q 1403 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-54, -55, -57, -60, -61, -64]) + (countLit q [-65, -67, -70, -71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64]) (l₂ := [-65, -67, -70, -71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1401)) (countLit q [-54, -55, -57, -60, -61, -64]) (countLit q [-65, -67, -70, -71, -73, -76, -79]) (count1399 q) 2 1 (meaning1374 q) (meaning1392 q) (meaning1401 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1392 = false ∨ valuation q 1401 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1402 = true := by
  have hs : count1399 q = (countLit q [-54, -55, -57, -60, -61, -64]) + (countLit q [-65, -67, -70, -71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64]) (l₂ := [-65, -67, -70, -71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1402)) (countLit q [-54, -55, -57, -60, -61, -64]) (countLit q [-65, -67, -70, -71, -73, -76, -79]) (count1399 q) 2 2 (meaning1374 q) (meaning1393 q) (meaning1402 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1393 = false ∨ valuation q 1402 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1403 = true := by
  have hs : count1399 q = (countLit q [-54, -55, -57, -60, -61, -64]) + (countLit q [-65, -67, -70, -71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64]) (l₂ := [-65, -67, -70, -71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1403)) (countLit q [-54, -55, -57, -60, -61, -64]) (countLit q [-65, -67, -70, -71, -73, -76, -79]) (count1399 q) 2 3 (meaning1374 q) (meaning1394 q) (meaning1403 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1394 = false ∨ valuation q 1403 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1403 = true := by
  have hs : count1399 q = (countLit q [-54, -55, -57, -60, -61, -64]) + (countLit q [-65, -67, -70, -71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64]) (l₂ := [-65, -67, -70, -71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1403)) (countLit q [-54, -55, -57, -60, -61, -64]) (countLit q [-65, -67, -70, -71, -73, -76, -79]) (count1399 q) 3 2 (meaning1375 q) (meaning1393 q) (meaning1403 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1393 = false ∨ valuation q 1403 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1412 = true := by
  have hs : count1412 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (1412)) (countLit q [-82]) (countLit q [-83]) (count1412 q) 1 (meaningNeg83 q) (meaning1412 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1412 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1412 = true := by
  have hs : count1412 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1412)) (countLit q [-82]) (countLit q [-83]) (count1412 q) 1 (meaningNeg82 q) (meaning1412 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1412 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 83 = true ∨ valuationOf q 1413 = true := by
  have hs : count1412 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-83)) (literal (valuationOf q) (1413)) (countLit q [-82]) (countLit q [-83]) (count1412 q) 1 1 (meaningNeg82 q) (meaningNeg83 q) (meaning1413 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 83)) = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 83 = true ∨ valuation q 1413 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-81]) + (countLit q [-82, -83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -83])
  have hm := merge_right (literal (valuationOf q) (1412)) (literal (valuationOf q) (1414)) (countLit q [-81]) (countLit q [-82, -83]) (count1414 q) 1 (meaning1412 q) (meaning1414 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1414 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-81]) + (countLit q [-82, -83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -83])
  have hm := merge_right (literal (valuationOf q) (1413)) (literal (valuationOf q) (1415)) (countLit q [-81]) (countLit q [-82, -83]) (count1414 q) 2 (meaning1413 q) (meaning1415 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1415 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-81]) + (countLit q [-82, -83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -83])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1414)) (countLit q [-81]) (countLit q [-82, -83]) (count1414 q) 1 (meaningNeg81 q) (meaning1414 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1414 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1412 = false ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-81]) + (countLit q [-82, -83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -83])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1415)) (countLit q [-81]) (countLit q [-82, -83]) (count1414 q) 1 1 (meaningNeg81 q) (meaning1412 q) (meaning1415 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1412 = false ∨ valuation q 1415 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1413 = false ∨ valuationOf q 1416 = true := by
  have hs : count1414 q = (countLit q [-81]) + (countLit q [-82, -83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -83])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1416)) (countLit q [-81]) (countLit q [-82, -83]) (count1414 q) 1 2 (meaningNeg81 q) (meaning1413 q) (meaning1416 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1413 = false ∨ valuation q 1416 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1417 = true := by
  have hs : count1417 q = (countLit q [-86]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1417)) (countLit q [-86]) (countLit q [-88]) (count1417 q) 1 (meaningNeg88 q) (meaning1417 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1417 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1417 = true := by
  have hs : count1417 q = (countLit q [-86]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1417)) (countLit q [-86]) (countLit q [-88]) (count1417 q) 1 (meaningNeg86 q) (meaning1417 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1417 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 88 = true ∨ valuationOf q 1418 = true := by
  have hs : count1417 q = (countLit q [-86]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (1418)) (countLit q [-86]) (countLit q [-88]) (count1417 q) 1 1 (meaningNeg86 q) (meaningNeg88 q) (meaning1418 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 1418 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1419 = true := by
  have hs : count1419 q = (countLit q [-90]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1419)) (countLit q [-90]) (countLit q [-93]) (count1419 q) 1 (meaningNeg93 q) (meaning1419 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1419 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1419 = true := by
  have hs : count1419 q = (countLit q [-90]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1419)) (countLit q [-90]) (countLit q [-93]) (count1419 q) 1 (meaningNeg90 q) (meaning1419 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1419 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1420 = true := by
  have hs : count1419 q = (countLit q [-90]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1420)) (countLit q [-90]) (countLit q [-93]) (count1419 q) 1 1 (meaningNeg90 q) (meaningNeg93 q) (meaning1420 q) hs
  change (! (valuationOf q 90)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 93 = true ∨ valuation q 1420 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-86, -88]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-86, -88]) (l₂ := [-90, -93])
  have hm := merge_right (literal (valuationOf q) (1419)) (literal (valuationOf q) (1421)) (countLit q [-86, -88]) (countLit q [-90, -93]) (count1421 q) 1 (meaning1419 q) (meaning1421 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1421 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-86, -88]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-86, -88]) (l₂ := [-90, -93])
  have hm := merge_left (literal (valuationOf q) (1417)) (literal (valuationOf q) (1421)) (countLit q [-86, -88]) (countLit q [-90, -93]) (count1421 q) 1 (meaning1417 q) (meaning1421 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1421 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-86, -88]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-86, -88]) (l₂ := [-90, -93])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1422)) (countLit q [-86, -88]) (countLit q [-90, -93]) (count1421 q) 1 1 (meaning1417 q) (meaning1419 q) (meaning1422 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1419 = false ∨ valuation q 1422 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1423 = true := by
  have hs : count1421 q = (countLit q [-86, -88]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-86, -88]) (l₂ := [-90, -93])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1423)) (countLit q [-86, -88]) (countLit q [-90, -93]) (count1421 q) 1 2 (meaning1417 q) (meaning1420 q) (meaning1423 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1420 = false ∨ valuation q 1423 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-86, -88]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-86, -88]) (l₂ := [-90, -93])
  have hm := merge_left (literal (valuationOf q) (1418)) (literal (valuationOf q) (1422)) (countLit q [-86, -88]) (countLit q [-90, -93]) (count1421 q) 2 (meaning1418 q) (meaning1422 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1422 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1423 = true := by
  have hs : count1421 q = (countLit q [-86, -88]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-86, -88]) (l₂ := [-90, -93])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1423)) (countLit q [-86, -88]) (countLit q [-90, -93]) (count1421 q) 2 1 (meaning1418 q) (meaning1419 q) (meaning1423 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1419 = false ∨ valuation q 1423 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-81, -82, -83]) + (countLit q [-86, -88, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-86, -88, -90, -93])
  have hm := merge_right (literal (valuationOf q) (1422)) (literal (valuationOf q) (1426)) (countLit q [-81, -82, -83]) (countLit q [-86, -88, -90, -93]) (count1425 q) 2 (meaning1422 q) (meaning1426 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1426 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1427 = true := by
  have hs : count1425 q = (countLit q [-81, -82, -83]) + (countLit q [-86, -88, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-86, -88, -90, -93])
  have hm := merge_right (literal (valuationOf q) (1423)) (literal (valuationOf q) (1427)) (countLit q [-81, -82, -83]) (countLit q [-86, -88, -90, -93]) (count1425 q) 3 (meaning1423 q) (meaning1427 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1427 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-81, -82, -83]) + (countLit q [-86, -88, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-86, -88, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1426)) (countLit q [-81, -82, -83]) (countLit q [-86, -88, -90, -93]) (count1425 q) 1 1 (meaning1414 q) (meaning1421 q) (meaning1426 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1421 = false ∨ valuation q 1426 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true := by
  have hs : count1425 q = (countLit q [-81, -82, -83]) + (countLit q [-86, -88, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-86, -88, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1427)) (countLit q [-81, -82, -83]) (countLit q [-86, -88, -90, -93]) (count1425 q) 1 2 (meaning1414 q) (meaning1422 q) (meaning1427 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1422 = false ∨ valuation q 1427 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1428 = true := by
  have hs : count1425 q = (countLit q [-81, -82, -83]) + (countLit q [-86, -88, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-86, -88, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1428)) (countLit q [-81, -82, -83]) (countLit q [-86, -88, -90, -93]) (count1425 q) 1 3 (meaning1414 q) (meaning1423 q) (meaning1428 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1423 = false ∨ valuation q 1428 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-81, -82, -83]) + (countLit q [-86, -88, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-86, -88, -90, -93])
  have hm := merge_left (literal (valuationOf q) (1415)) (literal (valuationOf q) (1426)) (countLit q [-81, -82, -83]) (countLit q [-86, -88, -90, -93]) (count1425 q) 2 (meaning1415 q) (meaning1426 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1426 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1427 = true := by
  have hs : count1425 q = (countLit q [-81, -82, -83]) + (countLit q [-86, -88, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-86, -88, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1427)) (countLit q [-81, -82, -83]) (countLit q [-86, -88, -90, -93]) (count1425 q) 2 1 (meaning1415 q) (meaning1421 q) (meaning1427 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1421 = false ∨ valuation q 1427 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E246.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112246
