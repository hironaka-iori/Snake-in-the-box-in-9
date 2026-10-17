import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1541)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 4 1 (meaning1480 q) (meaning1525 q) (meaning1541 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1525 = false ∨ valuation q 1541 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1542)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 4 2 (meaning1480 q) (meaning1526 q) (meaning1542 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1526 = false ∨ valuation q 1542 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1543 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1543)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 4 3 (meaning1480 q) (meaning1527 q) (meaning1543 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1527 = false ∨ valuation q 1543 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1544 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1544)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 4 4 (meaning1480 q) (meaning1528 q) (meaning1544 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1528 = false ∨ valuation q 1544 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1542)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 5 1 (meaning1481 q) (meaning1525 q) (meaning1542 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1525 = false ∨ valuation q 1542 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1543 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1543)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 5 2 (meaning1481 q) (meaning1526 q) (meaning1543 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1526 = false ∨ valuation q 1543 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1544 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1544)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 5 3 (meaning1481 q) (meaning1527 q) (meaning1544 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1527 = false ∨ valuation q 1544 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1543 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1543)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 6 1 (meaning1482 q) (meaning1525 q) (meaning1543 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1525 = false ∨ valuation q 1543 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1544 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1544)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 6 2 (meaning1482 q) (meaning1526 q) (meaning1544 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1526 = false ∨ valuation q 1544 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1544 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1544)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 7 1 (meaning1483 q) (meaning1525 q) (meaning1544 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1525 = false ∨ valuation q 1544 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1560 = true := by
  have hs : count1549 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) + (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (l₂ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1560)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1549 q) 4 8 (meaning1432 q) (meaning1544 q) (meaning1560 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1544 = false ∨ valuation q 1560 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1560 = true := by
  have hs : count1549 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) + (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (l₂ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1560)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1549 q) 5 7 (meaning1433 q) (meaning1543 q) (meaning1560 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1543 = false ∨ valuation q 1560 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1560 = true := by
  have hs : count1549 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) + (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (l₂ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1560)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1549 q) 6 6 (meaning1434 q) (meaning1542 q) (meaning1560 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1542 = false ∨ valuation q 1560 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1560 = true := by
  have hs : count1549 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) + (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (l₂ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1560)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1549 q) 7 5 (meaning1435 q) (meaning1541 q) (meaning1560 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1541 = false ∨ valuation q 1560 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1560 = true := by
  have hs : count1549 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) + (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (l₂ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1560)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1549 q) 8 4 (meaning1436 q) (meaning1540 q) (meaning1560 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1540 = false ∨ valuation q 1560 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1560 = true := by
  have hs : count1549 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) + (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (l₂ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1560)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1549 q) 9 3 (meaning1437 q) (meaning1539 q) (meaning1560 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1539 = false ∨ valuation q 1560 = true := counterClause816 (baseVal q)

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false := by
  rw [value1560]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1549 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value1, value2, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (16 : Vertex) (17 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 14 = false := by
  rw [value3, value6, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (2 : Vertex) (6 : Vertex) (18 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value3, value6, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (2 : Vertex) (6 : Vertex) (258 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value10, value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (16 : Vertex) (17 : Vertex) (18 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 34 = false ∨ valuation q 35 = false := by
  rw [value24, value25, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (74 : Vertex) (75 : Vertex) (90 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 35 = false := by
  rw [value32, value33, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (88 : Vertex) (89 : Vertex) (90 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value82, value83, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (329 : Vertex) (331 : Vertex) (333 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 94 = false := by
  rw [value89, value90, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (340 : Vertex) (342 : Vertex) (348 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value95, value96, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (450 : Vertex) (451 : Vertex) (458 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value97, value98, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (452 : Vertex) (453 : Vertex) (468 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E183.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h⟩

end
end Snake9.Regrowth.E112183
