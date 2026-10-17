import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1378 = false ∨ valuationOf q 1381 = true := by
  have hs : count1379 q = (countLit q [-84, -86]) + (countLit q [-87, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -86]) (l₂ := [-87, -92])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1378)) (literal (valuationOf q) (1381)) (countLit q [-84, -86]) (countLit q [-87, -92]) (count1379 q) 1 2 (meaning1375 q) (meaning1378 q) (meaning1381 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1378 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1378 = false ∨ valuation q 1381 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1380 = true := by
  have hs : count1379 q = (countLit q [-84, -86]) + (countLit q [-87, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -86]) (l₂ := [-87, -92])
  have hm := merge_left (literal (valuationOf q) (1376)) (literal (valuationOf q) (1380)) (countLit q [-84, -86]) (countLit q [-87, -92]) (count1379 q) 2 (meaning1376 q) (meaning1380 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1380 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1381 = true := by
  have hs : count1379 q = (countLit q [-84, -86]) + (countLit q [-87, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -86]) (l₂ := [-87, -92])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1377)) (literal (valuationOf q) (1381)) (countLit q [-84, -86]) (countLit q [-87, -92]) (count1379 q) 2 1 (meaning1376 q) (meaning1377 q) (meaning1381 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1377 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1377 = false ∨ valuation q 1381 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_right (literal (valuationOf q) (1379)) (literal (valuationOf q) (1383)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 1 (meaning1379 q) (meaning1383 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1383 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_right (literal (valuationOf q) (1380)) (literal (valuationOf q) (1384)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 2 (meaning1380 q) (meaning1384 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1384 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1385 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_right (literal (valuationOf q) (1381)) (literal (valuationOf q) (1385)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 3 (meaning1381 q) (meaning1385 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1385 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_left (literal (valuationOf q) (1372)) (literal (valuationOf q) (1383)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 1 (meaning1372 q) (meaning1383 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1383 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1384)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 1 1 (meaning1372 q) (meaning1379 q) (meaning1384 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1379 = false ∨ valuation q 1384 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1385 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1385)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 1 2 (meaning1372 q) (meaning1380 q) (meaning1385 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1380 = false ∨ valuation q 1385 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1386 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1386)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 1 3 (meaning1372 q) (meaning1381 q) (meaning1386 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1381 = false ∨ valuation q 1386 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_left (literal (valuationOf q) (1373)) (literal (valuationOf q) (1384)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 2 (meaning1373 q) (meaning1384 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1384 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1385 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1385)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 2 1 (meaning1373 q) (meaning1379 q) (meaning1385 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1379 = false ∨ valuation q 1385 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1386 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1386)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 2 2 (meaning1373 q) (meaning1380 q) (meaning1386 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1380 = false ∨ valuation q 1386 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1387 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1387)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 2 3 (meaning1373 q) (meaning1381 q) (meaning1387 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1381 = false ∨ valuation q 1387 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1385 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_left (literal (valuationOf q) (1374)) (literal (valuationOf q) (1385)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 3 (meaning1374 q) (meaning1385 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1385 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1386 = true := by
  have hs : count1383 q = (countLit q [-78, -80, -82]) + (countLit q [-84, -86, -87, -92]) := List.countP_append (p := literal q) (l₁ := [-78, -80, -82]) (l₂ := [-84, -86, -87, -92])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1386)) (countLit q [-78, -80, -82]) (countLit q [-84, -86, -87, -92]) (count1383 q) 3 1 (meaning1374 q) (meaning1379 q) (meaning1386 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1379 = false ∨ valuation q 1386 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1390 = true := by
  have hs : count1390 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1390)) (countLit q [-95]) (countLit q [-97]) (count1390 q) 1 (meaningNeg97 q) (meaning1390 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1390 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1391 = true := by
  have hs : count1390 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1391)) (countLit q [-95]) (countLit q [-97]) (count1390 q) 1 1 (meaningNeg95 q) (meaningNeg97 q) (meaning1391 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 1391 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuationOf q) (1390)) (literal (valuationOf q) (1392)) (countLit q [-93]) (countLit q [-95, -97]) (count1392 q) 1 (meaning1390 q) (meaning1392 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1392 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuationOf q) (1391)) (literal (valuationOf q) (1393)) (countLit q [-93]) (countLit q [-95, -97]) (count1392 q) 2 (meaning1391 q) (meaning1393 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1393 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1390 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (1390)) (literal (valuationOf q) (1393)) (countLit q [-93]) (countLit q [-95, -97]) (count1392 q) 1 1 (meaningNeg93 q) (meaning1390 q) (meaning1393 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1390 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1390 = false ∨ valuation q 1393 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1391 = false ∨ valuationOf q 1394 = true := by
  have hs : count1392 q = (countLit q [-93]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (1391)) (literal (valuationOf q) (1394)) (countLit q [-93]) (countLit q [-95, -97]) (count1392 q) 1 2 (meaningNeg93 q) (meaning1391 q) (meaning1394 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1391 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1391 = false ∨ valuation q 1394 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1395)) (countLit q [-99]) (countLit q [-101]) (count1395 q) 1 (meaningNeg101 q) (meaning1395 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1395 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1396 = true := by
  have hs : count1395 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1396)) (countLit q [-99]) (countLit q [-101]) (count1395 q) 1 1 (meaningNeg99 q) (meaningNeg101 q) (meaning1396 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 101 = true ∨ valuation q 1396 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1397)) (countLit q [-103]) (countLit q [-104]) (count1397 q) 1 (meaningNeg104 q) (meaning1397 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1397 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1397)) (countLit q [-103]) (countLit q [-104]) (count1397 q) 1 (meaningNeg103 q) (meaning1397 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1397 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 104 = true ∨ valuationOf q 1398 = true := by
  have hs : count1397 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-104)) (literal (valuationOf q) (1398)) (countLit q [-103]) (countLit q [-104]) (count1397 q) 1 1 (meaningNeg103 q) (meaningNeg104 q) (meaning1398 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 104)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 1398 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-99, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-103, -104])
  have hm := merge_left (literal (valuationOf q) (1395)) (literal (valuationOf q) (1399)) (countLit q [-99, -101]) (countLit q [-103, -104]) (count1399 q) 1 (meaning1395 q) (meaning1399 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1399 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-99, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-103, -104])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1397)) (literal (valuationOf q) (1400)) (countLit q [-99, -101]) (countLit q [-103, -104]) (count1399 q) 1 1 (meaning1395 q) (meaning1397 q) (meaning1400 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1397 = false ∨ valuation q 1400 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-99, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-103, -104])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1398)) (literal (valuationOf q) (1401)) (countLit q [-99, -101]) (countLit q [-103, -104]) (count1399 q) 1 2 (meaning1395 q) (meaning1398 q) (meaning1401 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1398 = false ∨ valuation q 1401 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-99, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-103, -104])
  have hm := merge_left (literal (valuationOf q) (1396)) (literal (valuationOf q) (1400)) (countLit q [-99, -101]) (countLit q [-103, -104]) (count1399 q) 2 (meaning1396 q) (meaning1400 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1400 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-99, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -101]) (l₂ := [-103, -104])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1397)) (literal (valuationOf q) (1401)) (countLit q [-99, -101]) (countLit q [-103, -104]) (count1399 q) 2 1 (meaning1396 q) (meaning1397 q) (meaning1401 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1397 = false ∨ valuation q 1401 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E094.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112094
