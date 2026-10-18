import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1522 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1522)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 2 4 (meaning1450 q) (meaning1506 q) (meaning1522 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1506 = false ∨ valuation q 1522 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1523 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1523)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 2 5 (meaning1450 q) (meaning1507 q) (meaning1523 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1507 = false ∨ valuation q 1523 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1524 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1524)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 2 6 (meaning1450 q) (meaning1508 q) (meaning1524 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1508 = false ∨ valuation q 1524 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1525 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1525)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 2 7 (meaning1450 q) (meaning1509 q) (meaning1525 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1509 = false ∨ valuation q 1525 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1522 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1522)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 3 3 (meaning1451 q) (meaning1505 q) (meaning1522 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1505 = false ∨ valuation q 1522 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1523 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1523)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 3 4 (meaning1451 q) (meaning1506 q) (meaning1523 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1506 = false ∨ valuation q 1523 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1524 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1524)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 3 5 (meaning1451 q) (meaning1507 q) (meaning1524 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1507 = false ∨ valuation q 1524 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1525 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1525)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 3 6 (meaning1451 q) (meaning1508 q) (meaning1525 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1508 = false ∨ valuation q 1525 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1523 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1523)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 4 3 (meaning1452 q) (meaning1505 q) (meaning1523 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1505 = false ∨ valuation q 1523 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1524 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1524)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 4 4 (meaning1452 q) (meaning1506 q) (meaning1524 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1506 = false ∨ valuation q 1524 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1525 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1525)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 4 5 (meaning1452 q) (meaning1507 q) (meaning1525 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1507 = false ∨ valuation q 1525 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1524 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1524)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 5 3 (meaning1453 q) (meaning1505 q) (meaning1524 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1505 = false ∨ valuation q 1524 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1525 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1525)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 5 4 (meaning1453 q) (meaning1506 q) (meaning1525 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1506 = false ∨ valuation q 1525 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1526 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1526)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 5 5 (meaning1453 q) (meaning1507 q) (meaning1526 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1507 = false ∨ valuation q 1526 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1523 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1523)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 6 1 (meaning1454 q) (meaning1503 q) (meaning1523 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1503 = false ∨ valuation q 1523 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1524 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1524)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 6 2 (meaning1454 q) (meaning1504 q) (meaning1524 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1504 = false ∨ valuation q 1524 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1525 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1525)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 6 3 (meaning1454 q) (meaning1505 q) (meaning1525 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1505 = false ∨ valuation q 1525 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1525 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1525)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 7 2 (meaning1455 q) (meaning1504 q) (meaning1525 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1504 = false ∨ valuation q 1525 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1525 = true := by
  have hs : count1517 q = (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) + (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (l₂ := [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1525)) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]) (countLit q [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1517 q) 8 1 (meaning1456 q) (meaning1503 q) (meaning1525 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1503 = false ∨ valuation q 1525 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1546 = true := by
  have hs : count1532 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) + (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (l₂ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1398)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1546)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1532 q) 5 10 (meaning1398 q) (meaning1526 q) (meaning1546 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1526 = false ∨ valuation q 1546 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1546 = true := by
  have hs : count1532 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) + (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (l₂ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1546)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1532 q) 6 9 (meaning1399 q) (meaning1525 q) (meaning1546 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1525 = false ∨ valuation q 1546 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1546 = true := by
  have hs : count1532 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) + (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (l₂ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1546)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1532 q) 7 8 (meaning1400 q) (meaning1524 q) (meaning1546 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1524 = false ∨ valuation q 1546 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1546 = true := by
  have hs : count1532 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) + (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (l₂ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1546)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1532 q) 8 7 (meaning1401 q) (meaning1523 q) (meaning1546 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1523 = false ∨ valuation q 1546 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1546 = true := by
  have hs : count1532 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) + (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (l₂ := [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1546)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (countLit q [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]) (count1532 q) 9 6 (meaning1402 q) (meaning1522 q) (meaning1546 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1522 = false ∨ valuation q 1546 = true := counterClause632 (baseVal q)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false := by
  rw [value1546]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1532 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value16, value17, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (170 : Vertex) (171 : Vertex) (186 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value31, value32, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (202 : Vertex) (203 : Vertex) (218 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value43, value44, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (259 : Vertex) (273 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value49, value50, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (270 : Vertex) (271 : Vertex) (286 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 59 = false ∨ valuation q 71 = false ∨ valuation q 76 = false := by
  rw [value55, value59, value71, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (278 : Vertex) (286 : Vertex) (342 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value65, value66, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (330 : Vertex) (331 : Vertex) (346 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value83, value84, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (430 : Vertex) (431 : Vertex) (446 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E166.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112166
