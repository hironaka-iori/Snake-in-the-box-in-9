import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1439 = true := by
  have hs : count1438 q = (countLit q [-74, -75]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -80])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1439)) (countLit q [-74, -75]) (countLit q [-78, -80]) (count1438 q) 1 1 (meaning1434 q) (meaning1436 q) (meaning1439 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1436 = false ∨ valuation q 1439 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1440 = true := by
  have hs : count1438 q = (countLit q [-74, -75]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -80])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1440)) (countLit q [-74, -75]) (countLit q [-78, -80]) (count1438 q) 1 2 (meaning1434 q) (meaning1437 q) (meaning1440 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1437 = false ∨ valuation q 1440 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1439 = true := by
  have hs : count1438 q = (countLit q [-74, -75]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -80])
  have hm := merge_left (literal (valuationOf q) (1435)) (literal (valuationOf q) (1439)) (countLit q [-74, -75]) (countLit q [-78, -80]) (count1438 q) 2 (meaning1435 q) (meaning1439 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1439 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1440 = true := by
  have hs : count1438 q = (countLit q [-74, -75]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -80])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1440)) (countLit q [-74, -75]) (countLit q [-78, -80]) (count1438 q) 2 1 (meaning1435 q) (meaning1436 q) (meaning1440 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1436 = false ∨ valuation q 1440 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1442 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-74, -75, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1438)) (literal (valuationOf q) (1442)) (countLit q [-68, -70, -71]) (countLit q [-74, -75, -78, -80]) (count1442 q) 1 (meaning1438 q) (meaning1442 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1442 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1443 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-74, -75, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1439)) (literal (valuationOf q) (1443)) (countLit q [-68, -70, -71]) (countLit q [-74, -75, -78, -80]) (count1442 q) 2 (meaning1439 q) (meaning1443 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1443 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1444 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-74, -75, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1440)) (literal (valuationOf q) (1444)) (countLit q [-68, -70, -71]) (countLit q [-74, -75, -78, -80]) (count1442 q) 3 (meaning1440 q) (meaning1444 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1444 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1442 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-74, -75, -78, -80])
  have hm := merge_left (literal (valuationOf q) (1431)) (literal (valuationOf q) (1442)) (countLit q [-68, -70, -71]) (countLit q [-74, -75, -78, -80]) (count1442 q) 1 (meaning1431 q) (meaning1442 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1442 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1443 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1443)) (countLit q [-68, -70, -71]) (countLit q [-74, -75, -78, -80]) (count1442 q) 1 1 (meaning1431 q) (meaning1438 q) (meaning1443 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1438 = false ∨ valuation q 1443 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1444 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1444)) (countLit q [-68, -70, -71]) (countLit q [-74, -75, -78, -80]) (count1442 q) 1 2 (meaning1431 q) (meaning1439 q) (meaning1444 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1439 = false ∨ valuation q 1444 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1445 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1445)) (countLit q [-68, -70, -71]) (countLit q [-74, -75, -78, -80]) (count1442 q) 1 3 (meaning1431 q) (meaning1440 q) (meaning1445 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1440 = false ∨ valuation q 1445 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1443 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-74, -75, -78, -80])
  have hm := merge_left (literal (valuationOf q) (1432)) (literal (valuationOf q) (1443)) (countLit q [-68, -70, -71]) (countLit q [-74, -75, -78, -80]) (count1442 q) 2 (meaning1432 q) (meaning1443 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1443 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1444 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1444)) (countLit q [-68, -70, -71]) (countLit q [-74, -75, -78, -80]) (count1442 q) 2 1 (meaning1432 q) (meaning1438 q) (meaning1444 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1438 = false ∨ valuation q 1444 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1445 = true := by
  have hs : count1442 q = (countLit q [-68, -70, -71]) + (countLit q [-74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-68, -70, -71]) (l₂ := [-74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1445)) (countLit q [-68, -70, -71]) (countLit q [-74, -75, -78, -80]) (count1442 q) 2 2 (meaning1432 q) (meaning1439 q) (meaning1445 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1439 = false ∨ valuation q 1445 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1422)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1450)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 1 1 (meaning1422 q) (meaning1442 q) (meaning1450 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1442 = false ∨ valuation q 1450 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1422)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1451)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 1 2 (meaning1422 q) (meaning1443 q) (meaning1451 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1443 = false ∨ valuation q 1451 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1422)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1452)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 1 3 (meaning1422 q) (meaning1444 q) (meaning1452 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1444 = false ∨ valuation q 1452 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1422)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1453)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 1 4 (meaning1422 q) (meaning1445 q) (meaning1453 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1445 = false ∨ valuation q 1453 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_left (literal (valuationOf q) (1423)) (literal (valuationOf q) (1450)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 2 (meaning1423 q) (meaning1450 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1450 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1451)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 2 1 (meaning1423 q) (meaning1442 q) (meaning1451 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1442 = false ∨ valuation q 1451 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1452)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 2 2 (meaning1423 q) (meaning1443 q) (meaning1452 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1443 = false ∨ valuation q 1452 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1453)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 2 3 (meaning1423 q) (meaning1444 q) (meaning1453 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1444 = false ∨ valuation q 1453 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1454 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1454)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 2 4 (meaning1423 q) (meaning1445 q) (meaning1454 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1445 = false ∨ valuation q 1454 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_left (literal (valuationOf q) (1424)) (literal (valuationOf q) (1451)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 3 (meaning1424 q) (meaning1451 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1451 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1452)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 3 1 (meaning1424 q) (meaning1442 q) (meaning1452 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1442 = false ∨ valuation q 1452 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1453)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 3 2 (meaning1424 q) (meaning1443 q) (meaning1453 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1443 = false ∨ valuation q 1453 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1454 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1454)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 3 3 (meaning1424 q) (meaning1444 q) (meaning1454 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1444 = false ∨ valuation q 1454 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_left (literal (valuationOf q) (1425)) (literal (valuationOf q) (1452)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 4 (meaning1425 q) (meaning1452 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1452 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1453)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 4 1 (meaning1425 q) (meaning1442 q) (meaning1453 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1442 = false ∨ valuation q 1453 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1454 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1454)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 4 2 (meaning1425 q) (meaning1443 q) (meaning1454 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1443 = false ∨ valuation q 1454 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_left (literal (valuationOf q) (1426)) (literal (valuationOf q) (1453)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 5 (meaning1426 q) (meaning1453 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1453 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1454 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1454)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 5 1 (meaning1426 q) (meaning1442 q) (meaning1454 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1442 = false ∨ valuation q 1454 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E090.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112090
