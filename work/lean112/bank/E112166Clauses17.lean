import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-81]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-84, -86])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1465)) (countLit q [-81]) (countLit q [-84, -86]) (count1465 q) 1 (meaningNeg81 q) (meaning1465 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1465 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-81]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-84, -86])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1466)) (countLit q [-81]) (countLit q [-84, -86]) (count1465 q) 1 1 (meaningNeg81 q) (meaning1463 q) (meaning1466 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1463 = false ∨ valuation q 1466 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-81]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-84, -86])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1467)) (countLit q [-81]) (countLit q [-84, -86]) (count1465 q) 1 2 (meaningNeg81 q) (meaning1464 q) (meaning1467 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1464 = false ∨ valuation q 1467 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1468 = true := by
  have hs : count1468 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1468)) (countLit q [-87]) (countLit q [-90]) (count1468 q) 1 (meaningNeg90 q) (meaning1468 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1468 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1468 = true := by
  have hs : count1468 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1468)) (countLit q [-87]) (countLit q [-90]) (count1468 q) 1 (meaningNeg87 q) (meaning1468 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1468 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 90 = true ∨ valuationOf q 1469 = true := by
  have hs : count1468 q = (countLit q [-87]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (1469)) (countLit q [-87]) (countLit q [-90]) (count1468 q) 1 1 (meaningNeg87 q) (meaningNeg90 q) (meaning1469 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 90 = true ∨ valuation q 1469 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1470)) (countLit q [-92]) (countLit q [-93]) (count1470 q) 1 (meaningNeg93 q) (meaning1470 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1470 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1470)) (countLit q [-92]) (countLit q [-93]) (count1470 q) 1 (meaningNeg92 q) (meaning1470 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1470 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1471)) (countLit q [-92]) (countLit q [-93]) (count1470 q) 1 1 (meaningNeg92 q) (meaningNeg93 q) (meaning1471 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 1471 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-87, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -90]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1470)) (literal (valuationOf q) (1472)) (countLit q [-87, -90]) (countLit q [-92, -93]) (count1472 q) 1 (meaning1470 q) (meaning1472 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1472 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-87, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -90]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1471)) (literal (valuationOf q) (1473)) (countLit q [-87, -90]) (countLit q [-92, -93]) (count1472 q) 2 (meaning1471 q) (meaning1473 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1473 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-87, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -90]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (1468)) (literal (valuationOf q) (1472)) (countLit q [-87, -90]) (countLit q [-92, -93]) (count1472 q) 1 (meaning1468 q) (meaning1472 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1472 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-87, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -90]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1473)) (countLit q [-87, -90]) (countLit q [-92, -93]) (count1472 q) 1 1 (meaning1468 q) (meaning1470 q) (meaning1473 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1470 = false ∨ valuation q 1473 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true := by
  have hs : count1472 q = (countLit q [-87, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -90]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1474)) (countLit q [-87, -90]) (countLit q [-92, -93]) (count1472 q) 1 2 (meaning1468 q) (meaning1471 q) (meaning1474 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1471 = false ∨ valuation q 1474 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-87, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -90]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (1469)) (literal (valuationOf q) (1473)) (countLit q [-87, -90]) (countLit q [-92, -93]) (count1472 q) 2 (meaning1469 q) (meaning1473 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1473 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1474 = true := by
  have hs : count1472 q = (countLit q [-87, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -90]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1474)) (countLit q [-87, -90]) (countLit q [-92, -93]) (count1472 q) 2 1 (meaning1469 q) (meaning1470 q) (meaning1474 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1470 = false ∨ valuation q 1474 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1476)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 1 (meaning1472 q) (meaning1476 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1476 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_right (literal (valuationOf q) (1473)) (literal (valuationOf q) (1477)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 2 (meaning1473 q) (meaning1477 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1477 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_right (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 3 (meaning1474 q) (meaning1478 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1478 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_left (literal (valuationOf q) (1465)) (literal (valuationOf q) (1476)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 1 (meaning1465 q) (meaning1476 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1476 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1477)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 1 1 (meaning1465 q) (meaning1472 q) (meaning1477 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1472 = false ∨ valuation q 1477 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1478)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 1 2 (meaning1465 q) (meaning1473 q) (meaning1478 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1473 = false ∨ valuation q 1478 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1479)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 1 3 (meaning1465 q) (meaning1474 q) (meaning1479 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1474 = false ∨ valuation q 1479 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_left (literal (valuationOf q) (1466)) (literal (valuationOf q) (1477)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 2 (meaning1466 q) (meaning1477 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1477 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1478)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 2 1 (meaning1466 q) (meaning1472 q) (meaning1478 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1472 = false ∨ valuation q 1478 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1479 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1479)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 2 2 (meaning1466 q) (meaning1473 q) (meaning1479 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1473 = false ∨ valuation q 1479 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1480)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 2 3 (meaning1466 q) (meaning1474 q) (meaning1480 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1474 = false ∨ valuation q 1480 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_left (literal (valuationOf q) (1467)) (literal (valuationOf q) (1478)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 3 (meaning1467 q) (meaning1478 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1478 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1479 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1479)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 3 1 (meaning1467 q) (meaning1472 q) (meaning1479 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1472 = false ∨ valuation q 1479 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1480 = true := by
  have hs : count1476 q = (countLit q [-81, -84, -86]) + (countLit q [-87, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -84, -86]) (l₂ := [-87, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1480)) (countLit q [-81, -84, -86]) (countLit q [-87, -90, -92, -93]) (count1476 q) 3 2 (meaning1467 q) (meaning1473 q) (meaning1480 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1473 = false ∨ valuation q 1480 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1483 = true := by
  have hs : count1483 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1483)) (countLit q [-98]) (countLit q [-101]) (count1483 q) 1 (meaningNeg101 q) (meaning1483 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1483 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1483 = true := by
  have hs : count1483 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1483)) (countLit q [-98]) (countLit q [-101]) (count1483 q) 1 (meaningNeg98 q) (meaning1483 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1483 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E166.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112166
