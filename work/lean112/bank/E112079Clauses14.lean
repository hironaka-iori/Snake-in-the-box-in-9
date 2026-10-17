import E112079Semantics
import B112E079Inputs
namespace Snake9.Regrowth.E112079
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1446)) (countLit q [-66]) (countLit q [-68]) (count1446 q) 1 (meaningNeg66 q) (meaning1446 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1446 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-65]) + (countLit q [-66, -68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66, -68])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1448)) (countLit q [-65]) (countLit q [-66, -68]) (count1448 q) 1 (meaning1446 q) (meaning1448 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1448 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-65]) + (countLit q [-66, -68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66, -68])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1448)) (countLit q [-65]) (countLit q [-66, -68]) (count1448 q) 1 (meaningNeg65 q) (meaning1448 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1448 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1451 = true := by
  have hs : count1451 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -66, -68]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -66, -68])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1451)) (countLit q [-59, -61, -63]) (countLit q [-65, -66, -68]) (count1451 q) 1 (meaning1448 q) (meaning1451 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1451 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1451 = true := by
  have hs : count1451 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -66, -68]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -66, -68])
  have hm := merge_left (literal (valuationOf q) (1443)) (literal (valuationOf q) (1451)) (countLit q [-59, -61, -63]) (countLit q [-65, -66, -68]) (count1451 q) 1 (meaning1443 q) (meaning1451 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1451 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1451 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -66, -68]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -66, -68])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-59, -61, -63]) (countLit q [-65, -66, -68]) (count1451 q) 1 1 (meaning1443 q) (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1448 = false ∨ valuation q 1452 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1452 = true := by
  have hs : count1451 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -66, -68]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -66, -68])
  have hm := merge_left (literal (valuationOf q) (1444)) (literal (valuationOf q) (1452)) (countLit q [-59, -61, -63]) (countLit q [-65, -66, -68]) (count1451 q) 2 (meaning1444 q) (meaning1452 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1452 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true := by
  have hs : count1451 q = (countLit q [-59, -61, -63]) + (countLit q [-65, -66, -68]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63]) (l₂ := [-65, -66, -68])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1453)) (countLit q [-59, -61, -63]) (countLit q [-65, -66, -68]) (count1451 q) 2 1 (meaning1444 q) (meaning1448 q) (meaning1453 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1448 = false ∨ valuation q 1453 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1457)) (countLit q [-73]) (countLit q [-74]) (count1457 q) 1 (meaningNeg74 q) (meaning1457 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1457 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1457)) (countLit q [-73]) (countLit q [-74]) (count1457 q) 1 (meaningNeg73 q) (meaning1457 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1457 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-71]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73, -74])
  have hm := merge_right (literal (valuationOf q) (1457)) (literal (valuationOf q) (1459)) (countLit q [-71]) (countLit q [-73, -74]) (count1459 q) 1 (meaning1457 q) (meaning1459 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1459 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-71]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73, -74])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1459)) (countLit q [-71]) (countLit q [-73, -74]) (count1459 q) 1 (meaningNeg71 q) (meaning1459 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1459 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1462)) (countLit q [-76]) (countLit q [-79]) (count1462 q) 1 (meaningNeg79 q) (meaning1462 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1462 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1462)) (countLit q [-76]) (countLit q [-79]) (count1462 q) 1 (meaningNeg76 q) (meaning1462 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1462 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1464)) (countLit q [-81]) (countLit q [-82]) (count1464 q) 1 (meaningNeg82 q) (meaning1464 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1464 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1464)) (countLit q [-81]) (countLit q [-82]) (count1464 q) 1 (meaningNeg81 q) (meaning1464 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1464 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1466 = true := by
  have hs : count1466 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1466)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count1466 q) 1 (meaning1464 q) (meaning1466 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1466 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1466 = true := by
  have hs : count1466 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_left (literal (valuationOf q) (1462)) (literal (valuationOf q) (1466)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count1466 q) 1 (meaning1462 q) (meaning1466 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1466 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1467)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count1466 q) 1 1 (meaning1462 q) (meaning1464 q) (meaning1467 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1464 = false ∨ valuation q 1467 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-71, -73, -74]) + (countLit q [-76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -73, -74]) (l₂ := [-76, -79, -81, -82])
  have hm := merge_right (literal (valuationOf q) (1466)) (literal (valuationOf q) (1470)) (countLit q [-71, -73, -74]) (countLit q [-76, -79, -81, -82]) (count1470 q) 1 (meaning1466 q) (meaning1470 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1470 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-71, -73, -74]) + (countLit q [-76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -73, -74]) (l₂ := [-76, -79, -81, -82])
  have hm := merge_right (literal (valuationOf q) (1467)) (literal (valuationOf q) (1471)) (countLit q [-71, -73, -74]) (countLit q [-76, -79, -81, -82]) (count1470 q) 2 (meaning1467 q) (meaning1471 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1471 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-71, -73, -74]) + (countLit q [-76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -73, -74]) (l₂ := [-76, -79, -81, -82])
  have hm := merge_left (literal (valuationOf q) (1459)) (literal (valuationOf q) (1470)) (countLit q [-71, -73, -74]) (countLit q [-76, -79, -81, -82]) (count1470 q) 1 (meaning1459 q) (meaning1470 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1470 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-71, -73, -74]) + (countLit q [-76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -73, -74]) (l₂ := [-76, -79, -81, -82])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1471)) (countLit q [-71, -73, -74]) (countLit q [-76, -79, -81, -82]) (count1470 q) 1 1 (meaning1459 q) (meaning1466 q) (meaning1471 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1466 = false ∨ valuation q 1471 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1472 = true := by
  have hs : count1470 q = (countLit q [-71, -73, -74]) + (countLit q [-76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-71, -73, -74]) (l₂ := [-76, -79, -81, -82])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1472)) (countLit q [-71, -73, -74]) (countLit q [-76, -79, -81, -82]) (count1470 q) 1 2 (meaning1459 q) (meaning1467 q) (meaning1472 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1467 = false ∨ valuation q 1472 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-59, -61, -63, -65, -66, -68]) + (countLit q [-71, -73, -74, -76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68]) (l₂ := [-71, -73, -74, -76, -79, -81, -82])
  have hm := merge_right (literal (valuationOf q) (1471)) (literal (valuationOf q) (1478)) (countLit q [-59, -61, -63, -65, -66, -68]) (countLit q [-71, -73, -74, -76, -79, -81, -82]) (count1477 q) 2 (meaning1471 q) (meaning1478 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1478 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-59, -61, -63, -65, -66, -68]) + (countLit q [-71, -73, -74, -76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68]) (l₂ := [-71, -73, -74, -76, -79, -81, -82])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1479)) (countLit q [-59, -61, -63, -65, -66, -68]) (countLit q [-71, -73, -74, -76, -79, -81, -82]) (count1477 q) 3 (meaning1472 q) (meaning1479 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1479 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-59, -61, -63, -65, -66, -68]) + (countLit q [-71, -73, -74, -76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68]) (l₂ := [-71, -73, -74, -76, -79, -81, -82])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1478)) (countLit q [-59, -61, -63, -65, -66, -68]) (countLit q [-71, -73, -74, -76, -79, -81, -82]) (count1477 q) 1 1 (meaning1451 q) (meaning1470 q) (meaning1478 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1470 = false ∨ valuation q 1478 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-59, -61, -63, -65, -66, -68]) + (countLit q [-71, -73, -74, -76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68]) (l₂ := [-71, -73, -74, -76, -79, -81, -82])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1479)) (countLit q [-59, -61, -63, -65, -66, -68]) (countLit q [-71, -73, -74, -76, -79, -81, -82]) (count1477 q) 1 2 (meaning1451 q) (meaning1471 q) (meaning1479 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1471 = false ∨ valuation q 1479 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-59, -61, -63, -65, -66, -68]) + (countLit q [-71, -73, -74, -76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68]) (l₂ := [-71, -73, -74, -76, -79, -81, -82])
  have hm := merge_left (literal (valuationOf q) (1452)) (literal (valuationOf q) (1478)) (countLit q [-59, -61, -63, -65, -66, -68]) (countLit q [-71, -73, -74, -76, -79, -81, -82]) (count1477 q) 2 (meaning1452 q) (meaning1478 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1478 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-59, -61, -63, -65, -66, -68]) + (countLit q [-71, -73, -74, -76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68]) (l₂ := [-71, -73, -74, -76, -79, -81, -82])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1479)) (countLit q [-59, -61, -63, -65, -66, -68]) (countLit q [-71, -73, -74, -76, -79, -81, -82]) (count1477 q) 2 1 (meaning1452 q) (meaning1470 q) (meaning1479 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1470 = false ∨ valuation q 1479 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-59, -61, -63, -65, -66, -68]) + (countLit q [-71, -73, -74, -76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68]) (l₂ := [-71, -73, -74, -76, -79, -81, -82])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1480)) (countLit q [-59, -61, -63, -65, -66, -68]) (countLit q [-71, -73, -74, -76, -79, -81, -82]) (count1477 q) 2 2 (meaning1452 q) (meaning1471 q) (meaning1480 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1471 = false ∨ valuation q 1480 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-59, -61, -63, -65, -66, -68]) + (countLit q [-71, -73, -74, -76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68]) (l₂ := [-71, -73, -74, -76, -79, -81, -82])
  have hm := merge_left (literal (valuationOf q) (1453)) (literal (valuationOf q) (1479)) (countLit q [-59, -61, -63, -65, -66, -68]) (countLit q [-71, -73, -74, -76, -79, -81, -82]) (count1477 q) 3 (meaning1453 q) (meaning1479 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1479 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E079.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112079
