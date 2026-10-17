import E112079Semantics
import B112E079Inputs
namespace Snake9.Regrowth.E112079
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1480 = true := by
  have hs : count1477 q = (countLit q [-59, -61, -63, -65, -66, -68]) + (countLit q [-71, -73, -74, -76, -79, -81, -82]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68]) (l₂ := [-71, -73, -74, -76, -79, -81, -82])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1480)) (countLit q [-59, -61, -63, -65, -66, -68]) (countLit q [-71, -73, -74, -76, -79, -81, -82]) (count1477 q) 3 1 (meaning1453 q) (meaning1470 q) (meaning1480 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1470 = false ∨ valuation q 1480 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1489 = true := by
  have hs : count1489 q = (countLit q [-87]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1489)) (countLit q [-87]) (countLit q [-89]) (count1489 q) 1 (meaningNeg89 q) (meaning1489 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1489 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1489 = true := by
  have hs : count1489 q = (countLit q [-87]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1489)) (countLit q [-87]) (countLit q [-89]) (count1489 q) 1 (meaningNeg87 q) (meaning1489 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1489 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 89 = true ∨ valuationOf q 1490 = true := by
  have hs : count1489 q = (countLit q [-87]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-89)) (literal (valuationOf q) (1490)) (countLit q [-87]) (countLit q [-89]) (count1489 q) 1 1 (meaningNeg87 q) (meaningNeg89 q) (meaning1490 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 89)) = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 89 = true ∨ valuation q 1490 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1491 = true := by
  have hs : count1491 q = (countLit q [-84]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87, -89])
  have hm := merge_right (literal (valuationOf q) (1489)) (literal (valuationOf q) (1491)) (countLit q [-84]) (countLit q [-87, -89]) (count1491 q) 1 (meaning1489 q) (meaning1491 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1491 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1492 = true := by
  have hs : count1491 q = (countLit q [-84]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87, -89])
  have hm := merge_right (literal (valuationOf q) (1490)) (literal (valuationOf q) (1492)) (countLit q [-84]) (countLit q [-87, -89]) (count1491 q) 2 (meaning1490 q) (meaning1492 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1492 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1491 = true := by
  have hs : count1491 q = (countLit q [-84]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87, -89])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1491)) (countLit q [-84]) (countLit q [-87, -89]) (count1491 q) 1 (meaningNeg84 q) (meaning1491 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1491 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1489 = false ∨ valuationOf q 1492 = true := by
  have hs : count1491 q = (countLit q [-84]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87, -89])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1492)) (countLit q [-84]) (countLit q [-87, -89]) (count1491 q) 1 1 (meaningNeg84 q) (meaning1489 q) (meaning1492 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1489 = false ∨ valuation q 1492 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-93]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1494)) (countLit q [-93]) (countLit q [-96]) (count1494 q) 1 (meaningNeg93 q) (meaning1494 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1494 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-90]) + (countLit q [-93, -96]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93, -96])
  have hm := merge_right (literal (valuationOf q) (1494)) (literal (valuationOf q) (1496)) (countLit q [-90]) (countLit q [-93, -96]) (count1496 q) 1 (meaning1494 q) (meaning1496 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1496 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-90]) + (countLit q [-93, -96]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93, -96])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1496)) (countLit q [-90]) (countLit q [-93, -96]) (count1496 q) 1 (meaningNeg90 q) (meaning1496 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1496 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-90]) + (countLit q [-93, -96]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93, -96])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1497)) (countLit q [-90]) (countLit q [-93, -96]) (count1496 q) 1 1 (meaningNeg90 q) (meaning1494 q) (meaning1497 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1494 = false ∨ valuation q 1497 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-84, -87, -89]) + (countLit q [-90, -93, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89]) (l₂ := [-90, -93, -96])
  have hm := merge_right (literal (valuationOf q) (1496)) (literal (valuationOf q) (1499)) (countLit q [-84, -87, -89]) (countLit q [-90, -93, -96]) (count1499 q) 1 (meaning1496 q) (meaning1499 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1499 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-84, -87, -89]) + (countLit q [-90, -93, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89]) (l₂ := [-90, -93, -96])
  have hm := merge_right (literal (valuationOf q) (1497)) (literal (valuationOf q) (1500)) (countLit q [-84, -87, -89]) (countLit q [-90, -93, -96]) (count1499 q) 2 (meaning1497 q) (meaning1500 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1500 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-84, -87, -89]) + (countLit q [-90, -93, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89]) (l₂ := [-90, -93, -96])
  have hm := merge_left (literal (valuationOf q) (1491)) (literal (valuationOf q) (1499)) (countLit q [-84, -87, -89]) (countLit q [-90, -93, -96]) (count1499 q) 1 (meaning1491 q) (meaning1499 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1499 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-84, -87, -89]) + (countLit q [-90, -93, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89]) (l₂ := [-90, -93, -96])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1500)) (countLit q [-84, -87, -89]) (countLit q [-90, -93, -96]) (count1499 q) 1 1 (meaning1491 q) (meaning1496 q) (meaning1500 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1496 = false ∨ valuation q 1500 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1501 = true := by
  have hs : count1499 q = (countLit q [-84, -87, -89]) + (countLit q [-90, -93, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89]) (l₂ := [-90, -93, -96])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1501)) (countLit q [-84, -87, -89]) (countLit q [-90, -93, -96]) (count1499 q) 1 2 (meaning1491 q) (meaning1497 q) (meaning1501 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1497 = false ∨ valuation q 1501 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-84, -87, -89]) + (countLit q [-90, -93, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89]) (l₂ := [-90, -93, -96])
  have hm := merge_left (literal (valuationOf q) (1492)) (literal (valuationOf q) (1500)) (countLit q [-84, -87, -89]) (countLit q [-90, -93, -96]) (count1499 q) 2 (meaning1492 q) (meaning1500 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1500 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1501 = true := by
  have hs : count1499 q = (countLit q [-84, -87, -89]) + (countLit q [-90, -93, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89]) (l₂ := [-90, -93, -96])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1501)) (countLit q [-84, -87, -89]) (countLit q [-90, -93, -96]) (count1499 q) 2 1 (meaning1492 q) (meaning1496 q) (meaning1501 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1496 = false ∨ valuation q 1501 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1505)) (countLit q [-99]) (countLit q [-100]) (count1505 q) 1 (meaningNeg100 q) (meaning1505 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1505 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1505)) (countLit q [-99]) (countLit q [-100]) (count1505 q) 1 (meaningNeg99 q) (meaning1505 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1505 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1506 = true := by
  have hs : count1505 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1506)) (countLit q [-99]) (countLit q [-100]) (count1505 q) 1 1 (meaningNeg99 q) (meaningNeg100 q) (meaning1506 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 1506 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -100])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (countLit q [-98]) (countLit q [-99, -100]) (count1507 q) 1 (meaning1505 q) (meaning1507 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -100])
  have hm := merge_right (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (countLit q [-98]) (countLit q [-99, -100]) (count1507 q) 2 (meaning1506 q) (meaning1508 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -100])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1507)) (countLit q [-98]) (countLit q [-99, -100]) (count1507 q) 1 (meaningNeg98 q) (meaning1507 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1507 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1508)) (countLit q [-98]) (countLit q [-99, -100]) (count1507 q) 1 1 (meaningNeg98 q) (meaning1505 q) (meaning1508 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1505 = false ∨ valuation q 1508 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1510)) (countLit q [-104]) (countLit q [-106]) (count1510 q) 1 (meaningNeg106 q) (meaning1510 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1510 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1510)) (countLit q [-104]) (countLit q [-106]) (count1510 q) 1 (meaningNeg104 q) (meaning1510 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1510 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1512)) (countLit q [-107]) (countLit q [-108]) (count1512 q) 1 (meaningNeg108 q) (meaning1512 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1512 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1512)) (countLit q [-107]) (countLit q [-108]) (count1512 q) 1 (meaningNeg107 q) (meaning1512 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1512 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1513)) (countLit q [-107]) (countLit q [-108]) (count1512 q) 1 1 (meaningNeg107 q) (meaningNeg108 q) (meaning1513 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 1513 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -108])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1514)) (countLit q [-104, -106]) (countLit q [-107, -108]) (count1514 q) 1 (meaning1512 q) (meaning1514 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1514 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E079.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112079
