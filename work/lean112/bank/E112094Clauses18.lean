import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1404 = true := by
  have hs : count1403 q = (countLit q [-93, -95, -97]) + (countLit q [-99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-93, -95, -97]) (l₂ := [-99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1399)) (literal (valuationOf q) (1404)) (countLit q [-93, -95, -97]) (countLit q [-99, -101, -103, -104]) (count1403 q) 1 1 (meaning1392 q) (meaning1399 q) (meaning1404 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1399 = false ∨ valuation q 1404 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1405 = true := by
  have hs : count1403 q = (countLit q [-93, -95, -97]) + (countLit q [-99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-93, -95, -97]) (l₂ := [-99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1405)) (countLit q [-93, -95, -97]) (countLit q [-99, -101, -103, -104]) (count1403 q) 1 2 (meaning1392 q) (meaning1400 q) (meaning1405 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1400 = false ∨ valuation q 1405 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1406 = true := by
  have hs : count1403 q = (countLit q [-93, -95, -97]) + (countLit q [-99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-93, -95, -97]) (l₂ := [-99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1406)) (countLit q [-93, -95, -97]) (countLit q [-99, -101, -103, -104]) (count1403 q) 1 3 (meaning1392 q) (meaning1401 q) (meaning1406 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1401 = false ∨ valuation q 1406 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1405 = true := by
  have hs : count1403 q = (countLit q [-93, -95, -97]) + (countLit q [-99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-93, -95, -97]) (l₂ := [-99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1399)) (literal (valuationOf q) (1405)) (countLit q [-93, -95, -97]) (countLit q [-99, -101, -103, -104]) (count1403 q) 2 1 (meaning1393 q) (meaning1399 q) (meaning1405 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1399 = false ∨ valuation q 1405 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1406 = true := by
  have hs : count1403 q = (countLit q [-93, -95, -97]) + (countLit q [-99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-93, -95, -97]) (l₂ := [-99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1406)) (countLit q [-93, -95, -97]) (countLit q [-99, -101, -103, -104]) (count1403 q) 2 2 (meaning1393 q) (meaning1400 q) (meaning1406 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1400 = false ∨ valuation q 1406 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1407 = true := by
  have hs : count1403 q = (countLit q [-93, -95, -97]) + (countLit q [-99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-93, -95, -97]) (l₂ := [-99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1407)) (countLit q [-93, -95, -97]) (countLit q [-99, -101, -103, -104]) (count1403 q) 2 3 (meaning1393 q) (meaning1401 q) (meaning1407 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1401 = false ∨ valuation q 1407 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1406 = true := by
  have hs : count1403 q = (countLit q [-93, -95, -97]) + (countLit q [-99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-93, -95, -97]) (l₂ := [-99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1399)) (literal (valuationOf q) (1406)) (countLit q [-93, -95, -97]) (countLit q [-99, -101, -103, -104]) (count1403 q) 3 1 (meaning1394 q) (meaning1399 q) (meaning1406 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1399 = false ∨ valuation q 1406 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1407 = true := by
  have hs : count1403 q = (countLit q [-93, -95, -97]) + (countLit q [-99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-93, -95, -97]) (l₂ := [-99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1407)) (countLit q [-93, -95, -97]) (countLit q [-99, -101, -103, -104]) (count1403 q) 3 2 (meaning1394 q) (meaning1400 q) (meaning1407 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1400 = false ∨ valuation q 1407 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1412)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 1 2 (meaning1383 q) (meaning1404 q) (meaning1412 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1404 = false ∨ valuation q 1412 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1413 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1413)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 1 3 (meaning1383 q) (meaning1405 q) (meaning1413 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1405 = false ∨ valuation q 1413 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1414 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1414)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 1 4 (meaning1383 q) (meaning1406 q) (meaning1414 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1406 = false ∨ valuation q 1414 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1413 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1413)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 2 2 (meaning1384 q) (meaning1404 q) (meaning1413 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1404 = false ∨ valuation q 1413 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1414 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1414)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 2 3 (meaning1384 q) (meaning1405 q) (meaning1414 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1405 = false ∨ valuation q 1414 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1415 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1415)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 2 4 (meaning1384 q) (meaning1406 q) (meaning1415 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1406 = false ∨ valuation q 1415 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1416 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1416)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 2 5 (meaning1384 q) (meaning1407 q) (meaning1416 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1407 = false ∨ valuation q 1416 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1414 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1414)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 3 2 (meaning1385 q) (meaning1404 q) (meaning1414 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1404 = false ∨ valuation q 1414 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1415 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1415)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 3 3 (meaning1385 q) (meaning1405 q) (meaning1415 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1405 = false ∨ valuation q 1415 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1416 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1416)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 3 4 (meaning1385 q) (meaning1406 q) (meaning1416 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1406 = false ∨ valuation q 1416 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1415 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1415)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 4 2 (meaning1386 q) (meaning1404 q) (meaning1415 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1404 = false ∨ valuation q 1415 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1416 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1416)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 4 3 (meaning1386 q) (meaning1405 q) (meaning1416 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1405 = false ∨ valuation q 1416 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1416 = true := by
  have hs : count1410 q = (countLit q [-78, -80, -82, -84, -86, -87, -92]) + (countLit q [-93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82, -84, -86, -87, -92]) (l₂ := [-93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1416)) (countLit q [-78, -80, -82, -84, -86, -87, -92]) (countLit q [-93, -95, -97, -99, -101, -103, -104]) (count1410 q) 5 2 (meaning1387 q) (meaning1404 q) (meaning1416 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1404 = false ∨ valuation q 1416 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1428 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_right (literal (valuationOf q) (1415)) (literal (valuationOf q) (1428)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 6 (meaning1415 q) (meaning1428 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1428 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1429 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_right (literal (valuationOf q) (1416)) (literal (valuationOf q) (1429)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 7 (meaning1416 q) (meaning1429 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1429 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1427 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1427)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 1 4 (meaning1357 q) (meaning1413 q) (meaning1427 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1413 = false ∨ valuation q 1427 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1428 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1428)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 1 5 (meaning1357 q) (meaning1414 q) (meaning1428 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1414 = false ∨ valuation q 1428 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1429 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1429)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 1 6 (meaning1357 q) (meaning1415 q) (meaning1429 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1415 = false ∨ valuation q 1429 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1430 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1357)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1430)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 1 7 (meaning1357 q) (meaning1416 q) (meaning1430 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1416 = false ∨ valuation q 1430 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1427 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1358)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1427)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 2 3 (meaning1358 q) (meaning1412 q) (meaning1427 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1412 = false ∨ valuation q 1427 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1428 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1358)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1428)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 2 4 (meaning1358 q) (meaning1413 q) (meaning1428 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1413 = false ∨ valuation q 1428 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1429 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1358)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1429)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 2 5 (meaning1358 q) (meaning1414 q) (meaning1429 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1414 = false ∨ valuation q 1429 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1430 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1358)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1430)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 2 6 (meaning1358 q) (meaning1415 q) (meaning1430 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1415 = false ∨ valuation q 1430 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 1358 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1431 = true := by
  have hs : count1423 q = (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) + (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (l₂ := [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1358)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1431)) (countLit q [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]) (countLit q [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]) (count1423 q) 2 7 (meaning1358 q) (meaning1416 q) (meaning1431 q) hs
  change valuationOf q 1358 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 1358 = false ∨ valuation q 1416 = false ∨ valuation q 1431 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E094.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112094
