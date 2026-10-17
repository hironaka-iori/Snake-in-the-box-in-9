import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -79, -81, -83])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1471)) (countLit q [-69, -71, -73]) (countLit q [-76, -79, -81, -83]) (count1470 q) 2 (meaning1460 q) (meaning1471 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1471 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1472 = true := by
  have hs : count1470 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1472)) (countLit q [-69, -71, -73]) (countLit q [-76, -79, -81, -83]) (count1470 q) 2 1 (meaning1460 q) (meaning1466 q) (meaning1472 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1466 = false ∨ valuation q 1472 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1473 = true := by
  have hs : count1470 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1473)) (countLit q [-69, -71, -73]) (countLit q [-76, -79, -81, -83]) (count1470 q) 2 2 (meaning1460 q) (meaning1467 q) (meaning1473 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1467 = false ∨ valuation q 1473 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1473 = true := by
  have hs : count1470 q = (countLit q [-69, -71, -73]) + (countLit q [-76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-69, -71, -73]) (l₂ := [-76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1473)) (countLit q [-69, -71, -73]) (countLit q [-76, -79, -81, -83]) (count1470 q) 3 1 (meaning1461 q) (meaning1466 q) (meaning1473 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1466 = false ∨ valuation q 1473 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1478)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 1 1 (meaning1451 q) (meaning1470 q) (meaning1478 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1470 = false ∨ valuation q 1478 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1479)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 1 2 (meaning1451 q) (meaning1471 q) (meaning1479 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1471 = false ∨ valuation q 1479 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1480)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 1 3 (meaning1451 q) (meaning1472 q) (meaning1480 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1472 = false ∨ valuation q 1480 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_left (literal (valuationOf q) (1452)) (literal (valuationOf q) (1478)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 2 (meaning1452 q) (meaning1478 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1478 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1479)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 2 1 (meaning1452 q) (meaning1470 q) (meaning1479 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1470 = false ∨ valuation q 1479 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1480)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 2 2 (meaning1452 q) (meaning1471 q) (meaning1480 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1471 = false ∨ valuation q 1480 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1481 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1481)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 2 3 (meaning1452 q) (meaning1472 q) (meaning1481 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1472 = false ∨ valuation q 1481 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1482 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1482)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 2 4 (meaning1452 q) (meaning1473 q) (meaning1482 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1473 = false ∨ valuation q 1482 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_left (literal (valuationOf q) (1453)) (literal (valuationOf q) (1479)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 3 (meaning1453 q) (meaning1479 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1479 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1480)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 3 1 (meaning1453 q) (meaning1470 q) (meaning1480 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1470 = false ∨ valuation q 1480 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1481 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1481)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 3 2 (meaning1453 q) (meaning1471 q) (meaning1481 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1471 = false ∨ valuation q 1481 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1482 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1482)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 3 3 (meaning1453 q) (meaning1472 q) (meaning1482 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1472 = false ∨ valuation q 1482 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1483 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1483)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 3 4 (meaning1453 q) (meaning1473 q) (meaning1483 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1473 = false ∨ valuation q 1483 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_left (literal (valuationOf q) (1454)) (literal (valuationOf q) (1480)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 4 (meaning1454 q) (meaning1480 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1480 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1481 = true := by
  have hs : count1477 q = (countLit q [-57, -58, -61, -63, -65, -68]) + (countLit q [-69, -71, -73, -76, -79, -81, -83]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68]) (l₂ := [-69, -71, -73, -76, -79, -81, -83])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1481)) (countLit q [-57, -58, -61, -63, -65, -68]) (countLit q [-69, -71, -73, -76, -79, -81, -83]) (count1477 q) 4 1 (meaning1454 q) (meaning1470 q) (meaning1481 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1470 = false ∨ valuation q 1481 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1489 = true := by
  have hs : count1489 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1489)) (countLit q [-88]) (countLit q [-90]) (count1489 q) 1 (meaningNeg90 q) (meaning1489 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1489 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1489 = true := by
  have hs : count1489 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1489)) (countLit q [-88]) (countLit q [-90]) (count1489 q) 1 (meaningNeg88 q) (meaning1489 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1489 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 90 = true ∨ valuationOf q 1490 = true := by
  have hs : count1489 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (1490)) (countLit q [-88]) (countLit q [-90]) (count1489 q) 1 1 (meaningNeg88 q) (meaningNeg90 q) (meaning1490 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 1490 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1491 = true := by
  have hs : count1491 q = (countLit q [-84]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-88, -90])
  have hm := merge_right (literal (valuationOf q) (1489)) (literal (valuationOf q) (1491)) (countLit q [-84]) (countLit q [-88, -90]) (count1491 q) 1 (meaning1489 q) (meaning1491 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1491 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1492 = true := by
  have hs : count1491 q = (countLit q [-84]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-88, -90])
  have hm := merge_right (literal (valuationOf q) (1490)) (literal (valuationOf q) (1492)) (countLit q [-84]) (countLit q [-88, -90]) (count1491 q) 2 (meaning1490 q) (meaning1492 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1492 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1491 = true := by
  have hs : count1491 q = (countLit q [-84]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-88, -90])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1491)) (countLit q [-84]) (countLit q [-88, -90]) (count1491 q) 1 (meaningNeg84 q) (meaning1491 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1491 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1489 = false ∨ valuationOf q 1492 = true := by
  have hs : count1491 q = (countLit q [-84]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-88, -90])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1492)) (countLit q [-84]) (countLit q [-88, -90]) (count1491 q) 1 1 (meaningNeg84 q) (meaning1489 q) (meaning1492 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1489 = false ∨ valuation q 1492 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1490 = false ∨ valuationOf q 1493 = true := by
  have hs : count1491 q = (countLit q [-84]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-88, -90])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1493)) (countLit q [-84]) (countLit q [-88, -90]) (count1491 q) 1 2 (meaningNeg84 q) (meaning1490 q) (meaning1493 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1490 = false ∨ valuation q 1493 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-92]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1494)) (countLit q [-92]) (countLit q [-96]) (count1494 q) 1 (meaningNeg96 q) (meaning1494 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1494 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-92]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1494)) (countLit q [-92]) (countLit q [-96]) (count1494 q) 1 (meaningNeg92 q) (meaning1494 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1494 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1495 = true := by
  have hs : count1494 q = (countLit q [-92]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1495)) (countLit q [-92]) (countLit q [-96]) (count1494 q) 1 1 (meaningNeg92 q) (meaningNeg96 q) (meaning1495 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 96 = true ∨ valuation q 1495 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-91]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -96])
  have hm := merge_right (literal (valuationOf q) (1494)) (literal (valuationOf q) (1496)) (countLit q [-91]) (countLit q [-92, -96]) (count1496 q) 1 (meaning1494 q) (meaning1496 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1496 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-91]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -96])
  have hm := merge_right (literal (valuationOf q) (1495)) (literal (valuationOf q) (1497)) (countLit q [-91]) (countLit q [-92, -96]) (count1496 q) 2 (meaning1495 q) (meaning1497 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1497 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E183.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112183
