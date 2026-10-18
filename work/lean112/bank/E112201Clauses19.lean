import E112201Semantics
import B112E201Inputs
namespace Snake9.Regrowth.E112201
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -96]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -96])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1482)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -96]) (count1481 q) 2 (meaning1479 q) (meaning1482 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1482 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -96]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -96])
  have hm := merge_left (literal (valuationOf q) (1473)) (literal (valuationOf q) (1481)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -96]) (count1481 q) 1 (meaning1473 q) (meaning1481 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1481 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -96]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -96])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1482)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -96]) (count1481 q) 1 1 (meaning1473 q) (meaning1478 q) (meaning1482 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1478 = false ∨ valuation q 1482 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -96]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -96])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1483)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -96]) (count1481 q) 1 2 (meaning1473 q) (meaning1479 q) (meaning1483 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1479 = false ∨ valuation q 1483 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1484 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -96]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -96])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1484)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -96]) (count1481 q) 1 3 (meaning1473 q) (meaning1480 q) (meaning1484 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1480 = false ∨ valuation q 1484 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -96]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -96])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1483)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -96]) (count1481 q) 2 1 (meaning1474 q) (meaning1478 q) (meaning1483 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1478 = false ∨ valuation q 1483 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1484 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -96]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -96])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1484)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -96]) (count1481 q) 2 2 (meaning1474 q) (meaning1479 q) (meaning1484 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1479 = false ∨ valuation q 1484 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-85, -87, -88]) + (countLit q [-91, -94, -96]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88]) (l₂ := [-91, -94, -96])
  have hm := merge_left (literal (valuationOf q) (1475)) (literal (valuationOf q) (1483)) (countLit q [-85, -87, -88]) (countLit q [-91, -94, -96]) (count1481 q) 3 (meaning1475 q) (meaning1483 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1483 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1487)) (countLit q [-98]) (countLit q [-100]) (count1487 q) 1 (meaningNeg100 q) (meaning1487 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1487 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1487)) (countLit q [-98]) (countLit q [-100]) (count1487 q) 1 (meaningNeg98 q) (meaning1487 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1487 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1488 = true := by
  have hs : count1487 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1488)) (countLit q [-98]) (countLit q [-100]) (count1487 q) 1 1 (meaningNeg98 q) (meaningNeg100 q) (meaning1488 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 100 = true ∨ valuation q 1488 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1489 = true := by
  have hs : count1489 q = (countLit q [-97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98, -100])
  have hm := merge_right (literal (valuationOf q) (1487)) (literal (valuationOf q) (1489)) (countLit q [-97]) (countLit q [-98, -100]) (count1489 q) 1 (meaning1487 q) (meaning1489 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1489 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1490 = true := by
  have hs : count1489 q = (countLit q [-97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98, -100])
  have hm := merge_right (literal (valuationOf q) (1488)) (literal (valuationOf q) (1490)) (countLit q [-97]) (countLit q [-98, -100]) (count1489 q) 2 (meaning1488 q) (meaning1490 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1490 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1489 = true := by
  have hs : count1489 q = (countLit q [-97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98, -100])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1489)) (countLit q [-97]) (countLit q [-98, -100]) (count1489 q) 1 (meaningNeg97 q) (meaning1489 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1489 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1487 = false ∨ valuationOf q 1490 = true := by
  have hs : count1489 q = (countLit q [-97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1490)) (countLit q [-97]) (countLit q [-98, -100]) (count1489 q) 1 1 (meaningNeg97 q) (meaning1487 q) (meaning1490 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1487 = false ∨ valuation q 1490 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1492)) (countLit q [-103]) (countLit q [-105]) (count1492 q) 1 (meaningNeg105 q) (meaning1492 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1492 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1492)) (countLit q [-103]) (countLit q [-105]) (count1492 q) 1 (meaningNeg103 q) (meaning1492 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1492 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1494)) (countLit q [-106]) (countLit q [-107]) (count1494 q) 1 (meaningNeg107 q) (meaning1494 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1494 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1494)) (countLit q [-106]) (countLit q [-107]) (count1494 q) 1 (meaningNeg106 q) (meaning1494 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1494 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-103, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -107])
  have hm := merge_right (literal (valuationOf q) (1494)) (literal (valuationOf q) (1496)) (countLit q [-103, -105]) (countLit q [-106, -107]) (count1496 q) 1 (meaning1494 q) (meaning1496 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1496 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-103, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -107])
  have hm := merge_left (literal (valuationOf q) (1492)) (literal (valuationOf q) (1496)) (countLit q [-103, -105]) (countLit q [-106, -107]) (count1496 q) 1 (meaning1492 q) (meaning1496 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1496 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-103, -105]) + (countLit q [-106, -107]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-106, -107])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1497)) (countLit q [-103, -105]) (countLit q [-106, -107]) (count1496 q) 1 1 (meaning1492 q) (meaning1494 q) (meaning1497 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1494 = false ∨ valuation q 1497 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-97, -98, -100]) + (countLit q [-103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -100]) (l₂ := [-103, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1496)) (literal (valuationOf q) (1500)) (countLit q [-97, -98, -100]) (countLit q [-103, -105, -106, -107]) (count1500 q) 1 (meaning1496 q) (meaning1500 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1500 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-97, -98, -100]) + (countLit q [-103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -100]) (l₂ := [-103, -105, -106, -107])
  have hm := merge_left (literal (valuationOf q) (1489)) (literal (valuationOf q) (1500)) (countLit q [-97, -98, -100]) (countLit q [-103, -105, -106, -107]) (count1500 q) 1 (meaning1489 q) (meaning1500 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1500 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1501 = true := by
  have hs : count1500 q = (countLit q [-97, -98, -100]) + (countLit q [-103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -100]) (l₂ := [-103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1501)) (countLit q [-97, -98, -100]) (countLit q [-103, -105, -106, -107]) (count1500 q) 1 1 (meaning1489 q) (meaning1496 q) (meaning1501 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1496 = false ∨ valuation q 1501 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1502 = true := by
  have hs : count1500 q = (countLit q [-97, -98, -100]) + (countLit q [-103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -100]) (l₂ := [-103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1502)) (countLit q [-97, -98, -100]) (countLit q [-103, -105, -106, -107]) (count1500 q) 1 2 (meaning1489 q) (meaning1497 q) (meaning1502 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1497 = false ∨ valuation q 1502 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1502 = true := by
  have hs : count1500 q = (countLit q [-97, -98, -100]) + (countLit q [-103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-97, -98, -100]) (l₂ := [-103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1502)) (countLit q [-97, -98, -100]) (countLit q [-103, -105, -106, -107]) (count1500 q) 2 1 (meaning1490 q) (meaning1496 q) (meaning1502 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1496 = false ∨ valuation q 1502 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1500)) (literal (valuationOf q) (1507)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 1 (meaning1500 q) (meaning1507 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1507 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1501)) (literal (valuationOf q) (1508)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 2 (meaning1501 q) (meaning1508 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1508 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1509 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_right (literal (valuationOf q) (1502)) (literal (valuationOf q) (1509)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 3 (meaning1502 q) (meaning1509 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1509 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_left (literal (valuationOf q) (1481)) (literal (valuationOf q) (1507)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 1 (meaning1481 q) (meaning1507 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1507 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-85, -87, -88, -91, -94, -96]) + (countLit q [-97, -98, -100, -103, -105, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -91, -94, -96]) (l₂ := [-97, -98, -100, -103, -105, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1508)) (countLit q [-85, -87, -88, -91, -94, -96]) (countLit q [-97, -98, -100, -103, -105, -106, -107]) (count1507 q) 1 1 (meaning1481 q) (meaning1500 q) (meaning1508 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1500 = false ∨ valuation q 1508 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E201.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112201
