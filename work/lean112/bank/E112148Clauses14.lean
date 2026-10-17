import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1472)) (countLit q [-78]) (countLit q [-81]) (count1472 q) 1 (meaningNeg81 q) (meaning1472 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1472 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1472)) (countLit q [-78]) (countLit q [-81]) (count1472 q) 1 (meaningNeg78 q) (meaning1472 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1472 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1473)) (countLit q [-78]) (countLit q [-81]) (count1472 q) 1 1 (meaningNeg78 q) (meaningNeg81 q) (meaning1473 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 81 = true ∨ valuation q 1473 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-75, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -81])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (countLit q [-75, -77]) (countLit q [-78, -81]) (count1474 q) 1 (meaning1472 q) (meaning1474 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-75, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -81])
  have hm := merge_right (literal (valuationOf q) (1473)) (literal (valuationOf q) (1475)) (countLit q [-75, -77]) (countLit q [-78, -81]) (count1474 q) 2 (meaning1473 q) (meaning1475 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1475 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-75, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -81])
  have hm := merge_left (literal (valuationOf q) (1470)) (literal (valuationOf q) (1474)) (countLit q [-75, -77]) (countLit q [-78, -81]) (count1474 q) 1 (meaning1470 q) (meaning1474 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1474 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-75, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -81])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1475)) (countLit q [-75, -77]) (countLit q [-78, -81]) (count1474 q) 1 1 (meaning1470 q) (meaning1472 q) (meaning1475 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1472 = false ∨ valuation q 1475 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1476 = true := by
  have hs : count1474 q = (countLit q [-75, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -81])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1476)) (countLit q [-75, -77]) (countLit q [-78, -81]) (count1474 q) 1 2 (meaning1470 q) (meaning1473 q) (meaning1476 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1473 = false ∨ valuation q 1476 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-75, -77]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -81])
  have hm := merge_left (literal (valuationOf q) (1471)) (literal (valuationOf q) (1475)) (countLit q [-75, -77]) (countLit q [-78, -81]) (count1474 q) 2 (meaning1471 q) (meaning1475 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1475 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1478 = true := by
  have hs : count1478 q = (countLit q [-69, -71, -74]) + (countLit q [-75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -74]) (l₂ := [-75, -77, -78, -81])
  have hm := merge_right (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (countLit q [-69, -71, -74]) (countLit q [-75, -77, -78, -81]) (count1478 q) 1 (meaning1474 q) (meaning1478 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1478 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1479 = true := by
  have hs : count1478 q = (countLit q [-69, -71, -74]) + (countLit q [-75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -74]) (l₂ := [-75, -77, -78, -81])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1479)) (countLit q [-69, -71, -74]) (countLit q [-75, -77, -78, -81]) (count1478 q) 2 (meaning1475 q) (meaning1479 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1479 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-69, -71, -74]) + (countLit q [-75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -74]) (l₂ := [-75, -77, -78, -81])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1480)) (countLit q [-69, -71, -74]) (countLit q [-75, -77, -78, -81]) (count1478 q) 3 (meaning1476 q) (meaning1480 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1480 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1478 = true := by
  have hs : count1478 q = (countLit q [-69, -71, -74]) + (countLit q [-75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -74]) (l₂ := [-75, -77, -78, -81])
  have hm := merge_left (literal (valuationOf q) (1467)) (literal (valuationOf q) (1478)) (countLit q [-69, -71, -74]) (countLit q [-75, -77, -78, -81]) (count1478 q) 1 (meaning1467 q) (meaning1478 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1478 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true := by
  have hs : count1478 q = (countLit q [-69, -71, -74]) + (countLit q [-75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -74]) (l₂ := [-75, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1479)) (countLit q [-69, -71, -74]) (countLit q [-75, -77, -78, -81]) (count1478 q) 1 1 (meaning1467 q) (meaning1474 q) (meaning1479 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1474 = false ∨ valuation q 1479 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-69, -71, -74]) + (countLit q [-75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -74]) (l₂ := [-75, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1480)) (countLit q [-69, -71, -74]) (countLit q [-75, -77, -78, -81]) (count1478 q) 1 2 (meaning1467 q) (meaning1475 q) (meaning1480 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1475 = false ∨ valuation q 1480 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1481 = true := by
  have hs : count1478 q = (countLit q [-69, -71, -74]) + (countLit q [-75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -74]) (l₂ := [-75, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1481)) (countLit q [-69, -71, -74]) (countLit q [-75, -77, -78, -81]) (count1478 q) 1 3 (meaning1467 q) (meaning1476 q) (meaning1481 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1476 = false ∨ valuation q 1481 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1479 = true := by
  have hs : count1478 q = (countLit q [-69, -71, -74]) + (countLit q [-75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -74]) (l₂ := [-75, -77, -78, -81])
  have hm := merge_left (literal (valuationOf q) (1468)) (literal (valuationOf q) (1479)) (countLit q [-69, -71, -74]) (countLit q [-75, -77, -78, -81]) (count1478 q) 2 (meaning1468 q) (meaning1479 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1479 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-69, -71, -74]) + (countLit q [-75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -74]) (l₂ := [-75, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1480)) (countLit q [-69, -71, -74]) (countLit q [-75, -77, -78, -81]) (count1478 q) 2 1 (meaning1468 q) (meaning1474 q) (meaning1480 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1474 = false ∨ valuation q 1480 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true := by
  have hs : count1478 q = (countLit q [-69, -71, -74]) + (countLit q [-75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -74]) (l₂ := [-75, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1481)) (countLit q [-69, -71, -74]) (countLit q [-75, -77, -78, -81]) (count1478 q) 2 2 (meaning1468 q) (meaning1475 q) (meaning1481 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1475 = false ∨ valuation q 1481 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-57, -59, -61, -62, -64, -66, -67]) + (countLit q [-69, -71, -74, -75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67]) (l₂ := [-69, -71, -74, -75, -77, -78, -81])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1486)) (countLit q [-57, -59, -61, -62, -64, -66, -67]) (countLit q [-69, -71, -74, -75, -77, -78, -81]) (count1485 q) 2 (meaning1479 q) (meaning1486 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1486 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-57, -59, -61, -62, -64, -66, -67]) + (countLit q [-69, -71, -74, -75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67]) (l₂ := [-69, -71, -74, -75, -77, -78, -81])
  have hm := merge_right (literal (valuationOf q) (1480)) (literal (valuationOf q) (1487)) (countLit q [-57, -59, -61, -62, -64, -66, -67]) (countLit q [-69, -71, -74, -75, -77, -78, -81]) (count1485 q) 3 (meaning1480 q) (meaning1487 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1487 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-57, -59, -61, -62, -64, -66, -67]) + (countLit q [-69, -71, -74, -75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67]) (l₂ := [-69, -71, -74, -75, -77, -78, -81])
  have hm := merge_right (literal (valuationOf q) (1481)) (literal (valuationOf q) (1488)) (countLit q [-57, -59, -61, -62, -64, -66, -67]) (countLit q [-69, -71, -74, -75, -77, -78, -81]) (count1485 q) 4 (meaning1481 q) (meaning1488 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1488 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-57, -59, -61, -62, -64, -66, -67]) + (countLit q [-69, -71, -74, -75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67]) (l₂ := [-69, -71, -74, -75, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1486)) (countLit q [-57, -59, -61, -62, -64, -66, -67]) (countLit q [-69, -71, -74, -75, -77, -78, -81]) (count1485 q) 1 1 (meaning1458 q) (meaning1478 q) (meaning1486 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1478 = false ∨ valuation q 1486 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-57, -59, -61, -62, -64, -66, -67]) + (countLit q [-69, -71, -74, -75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67]) (l₂ := [-69, -71, -74, -75, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1487)) (countLit q [-57, -59, -61, -62, -64, -66, -67]) (countLit q [-69, -71, -74, -75, -77, -78, -81]) (count1485 q) 1 2 (meaning1458 q) (meaning1479 q) (meaning1487 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1479 = false ∨ valuation q 1487 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-57, -59, -61, -62, -64, -66, -67]) + (countLit q [-69, -71, -74, -75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67]) (l₂ := [-69, -71, -74, -75, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1488)) (countLit q [-57, -59, -61, -62, -64, -66, -67]) (countLit q [-69, -71, -74, -75, -77, -78, -81]) (count1485 q) 1 3 (meaning1458 q) (meaning1480 q) (meaning1488 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1480 = false ∨ valuation q 1488 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-57, -59, -61, -62, -64, -66, -67]) + (countLit q [-69, -71, -74, -75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67]) (l₂ := [-69, -71, -74, -75, -77, -78, -81])
  have hm := merge_left (literal (valuationOf q) (1459)) (literal (valuationOf q) (1486)) (countLit q [-57, -59, -61, -62, -64, -66, -67]) (countLit q [-69, -71, -74, -75, -77, -78, -81]) (count1485 q) 2 (meaning1459 q) (meaning1486 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1486 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-57, -59, -61, -62, -64, -66, -67]) + (countLit q [-69, -71, -74, -75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67]) (l₂ := [-69, -71, -74, -75, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1487)) (countLit q [-57, -59, -61, -62, -64, -66, -67]) (countLit q [-69, -71, -74, -75, -77, -78, -81]) (count1485 q) 2 1 (meaning1459 q) (meaning1478 q) (meaning1487 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1478 = false ∨ valuation q 1487 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-57, -59, -61, -62, -64, -66, -67]) + (countLit q [-69, -71, -74, -75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67]) (l₂ := [-69, -71, -74, -75, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1488)) (countLit q [-57, -59, -61, -62, -64, -66, -67]) (countLit q [-69, -71, -74, -75, -77, -78, -81]) (count1485 q) 2 2 (meaning1459 q) (meaning1479 q) (meaning1488 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1479 = false ∨ valuation q 1488 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-57, -59, -61, -62, -64, -66, -67]) + (countLit q [-69, -71, -74, -75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67]) (l₂ := [-69, -71, -74, -75, -77, -78, -81])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1487)) (countLit q [-57, -59, -61, -62, -64, -66, -67]) (countLit q [-69, -71, -74, -75, -77, -78, -81]) (count1485 q) 3 (meaning1460 q) (meaning1487 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1487 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-57, -59, -61, -62, -64, -66, -67]) + (countLit q [-69, -71, -74, -75, -77, -78, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -61, -62, -64, -66, -67]) (l₂ := [-69, -71, -74, -75, -77, -78, -81])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1488)) (countLit q [-57, -59, -61, -62, -64, -66, -67]) (countLit q [-69, -71, -74, -75, -77, -78, -81]) (count1485 q) 3 1 (meaning1460 q) (meaning1478 q) (meaning1488 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1478 = false ∨ valuation q 1488 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1499)) (countLit q [-85]) (countLit q [-86]) (count1499 q) 1 (meaningNeg86 q) (meaning1499 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1499 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1499)) (countLit q [-85]) (countLit q [-86]) (count1499 q) 1 (meaningNeg85 q) (meaning1499 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1499 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E148.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112148
