import E112079Semantics
import B112E079Inputs
namespace Snake9.Regrowth.E112079
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -108])
  have hm := merge_right (literal (valuationOf q) (1513)) (literal (valuationOf q) (1515)) (countLit q [-104, -106]) (countLit q [-107, -108]) (count1514 q) 2 (meaning1513 q) (meaning1515 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1515 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -108])
  have hm := merge_left (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-104, -106]) (countLit q [-107, -108]) (count1514 q) 1 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -108])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1515)) (countLit q [-104, -106]) (countLit q [-107, -108]) (count1514 q) 1 1 (meaning1510 q) (meaning1512 q) (meaning1515 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1512 = false ∨ valuation q 1515 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -100]) + (countLit q [-104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -100]) (l₂ := [-104, -106, -107, -108])
  have hm := merge_left (literal (valuationOf q) (1507)) (literal (valuationOf q) (1518)) (countLit q [-98, -99, -100]) (countLit q [-104, -106, -107, -108]) (count1518 q) 1 (meaning1507 q) (meaning1518 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1518 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -100]) + (countLit q [-104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -100]) (l₂ := [-104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1519)) (countLit q [-98, -99, -100]) (countLit q [-104, -106, -107, -108]) (count1518 q) 1 1 (meaning1507 q) (meaning1514 q) (meaning1519 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1514 = false ∨ valuation q 1519 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -100]) + (countLit q [-104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -100]) (l₂ := [-104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1520)) (countLit q [-98, -99, -100]) (countLit q [-104, -106, -107, -108]) (count1518 q) 1 2 (meaning1507 q) (meaning1515 q) (meaning1520 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1515 = false ∨ valuation q 1520 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -100]) + (countLit q [-104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -100]) (l₂ := [-104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1520)) (countLit q [-98, -99, -100]) (countLit q [-104, -106, -107, -108]) (count1518 q) 2 1 (meaning1508 q) (meaning1514 q) (meaning1520 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1514 = false ∨ valuation q 1520 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -100]) + (countLit q [-104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -100]) (l₂ := [-104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1521)) (countLit q [-98, -99, -100]) (countLit q [-104, -106, -107, -108]) (count1518 q) 2 2 (meaning1508 q) (meaning1515 q) (meaning1521 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1515 = false ∨ valuation q 1521 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-84, -87, -89, -90, -93, -96]) + (countLit q [-98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89, -90, -93, -96]) (l₂ := [-98, -99, -100, -104, -106, -107, -108])
  have hm := merge_right (literal (valuationOf q) (1519)) (literal (valuationOf q) (1526)) (countLit q [-84, -87, -89, -90, -93, -96]) (countLit q [-98, -99, -100, -104, -106, -107, -108]) (count1525 q) 2 (meaning1519 q) (meaning1526 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1526 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-84, -87, -89, -90, -93, -96]) + (countLit q [-98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89, -90, -93, -96]) (l₂ := [-98, -99, -100, -104, -106, -107, -108])
  have hm := merge_right (literal (valuationOf q) (1520)) (literal (valuationOf q) (1527)) (countLit q [-84, -87, -89, -90, -93, -96]) (countLit q [-98, -99, -100, -104, -106, -107, -108]) (count1525 q) 3 (meaning1520 q) (meaning1527 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1527 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1528 = true := by
  have hs : count1525 q = (countLit q [-84, -87, -89, -90, -93, -96]) + (countLit q [-98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89, -90, -93, -96]) (l₂ := [-98, -99, -100, -104, -106, -107, -108])
  have hm := merge_right (literal (valuationOf q) (1521)) (literal (valuationOf q) (1528)) (countLit q [-84, -87, -89, -90, -93, -96]) (countLit q [-98, -99, -100, -104, -106, -107, -108]) (count1525 q) 4 (meaning1521 q) (meaning1528 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1528 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-84, -87, -89, -90, -93, -96]) + (countLit q [-98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89, -90, -93, -96]) (l₂ := [-98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1526)) (countLit q [-84, -87, -89, -90, -93, -96]) (countLit q [-98, -99, -100, -104, -106, -107, -108]) (count1525 q) 1 1 (meaning1499 q) (meaning1518 q) (meaning1526 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1518 = false ∨ valuation q 1526 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-84, -87, -89, -90, -93, -96]) + (countLit q [-98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89, -90, -93, -96]) (l₂ := [-98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1527)) (countLit q [-84, -87, -89, -90, -93, -96]) (countLit q [-98, -99, -100, -104, -106, -107, -108]) (count1525 q) 1 2 (meaning1499 q) (meaning1519 q) (meaning1527 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1519 = false ∨ valuation q 1527 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1528 = true := by
  have hs : count1525 q = (countLit q [-84, -87, -89, -90, -93, -96]) + (countLit q [-98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89, -90, -93, -96]) (l₂ := [-98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1528)) (countLit q [-84, -87, -89, -90, -93, -96]) (countLit q [-98, -99, -100, -104, -106, -107, -108]) (count1525 q) 1 3 (meaning1499 q) (meaning1520 q) (meaning1528 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1520 = false ∨ valuation q 1528 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1529 = true := by
  have hs : count1525 q = (countLit q [-84, -87, -89, -90, -93, -96]) + (countLit q [-98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89, -90, -93, -96]) (l₂ := [-98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1529)) (countLit q [-84, -87, -89, -90, -93, -96]) (countLit q [-98, -99, -100, -104, -106, -107, -108]) (count1525 q) 1 4 (meaning1499 q) (meaning1521 q) (meaning1529 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1521 = false ∨ valuation q 1529 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-84, -87, -89, -90, -93, -96]) + (countLit q [-98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89, -90, -93, -96]) (l₂ := [-98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1527)) (countLit q [-84, -87, -89, -90, -93, -96]) (countLit q [-98, -99, -100, -104, -106, -107, -108]) (count1525 q) 2 1 (meaning1500 q) (meaning1518 q) (meaning1527 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1518 = false ∨ valuation q 1527 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1528 = true := by
  have hs : count1525 q = (countLit q [-84, -87, -89, -90, -93, -96]) + (countLit q [-98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89, -90, -93, -96]) (l₂ := [-98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1528)) (countLit q [-84, -87, -89, -90, -93, -96]) (countLit q [-98, -99, -100, -104, -106, -107, -108]) (count1525 q) 2 2 (meaning1500 q) (meaning1519 q) (meaning1528 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1519 = false ∨ valuation q 1528 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1529 = true := by
  have hs : count1525 q = (countLit q [-84, -87, -89, -90, -93, -96]) + (countLit q [-98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -87, -89, -90, -93, -96]) (l₂ := [-98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1529)) (countLit q [-84, -87, -89, -90, -93, -96]) (countLit q [-98, -99, -100, -104, -106, -107, -108]) (count1525 q) 3 2 (meaning1501 q) (meaning1519 q) (meaning1529 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1519 = false ∨ valuation q 1529 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) + (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (l₂ := [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1540)) (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) (count1537 q) 2 2 (meaning1478 q) (meaning1526 q) (meaning1540 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1526 = false ∨ valuation q 1540 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) + (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (l₂ := [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1541)) (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) (count1537 q) 2 3 (meaning1478 q) (meaning1527 q) (meaning1541 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1527 = false ∨ valuation q 1541 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) + (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (l₂ := [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1542)) (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) (count1537 q) 2 4 (meaning1478 q) (meaning1528 q) (meaning1542 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1528 = false ∨ valuation q 1542 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1543 = true := by
  have hs : count1537 q = (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) + (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (l₂ := [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1543)) (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) (count1537 q) 2 5 (meaning1478 q) (meaning1529 q) (meaning1543 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1529 = false ∨ valuation q 1543 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) + (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (l₂ := [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1541)) (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) (count1537 q) 3 2 (meaning1479 q) (meaning1526 q) (meaning1541 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1526 = false ∨ valuation q 1541 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) + (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (l₂ := [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1542)) (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) (count1537 q) 3 3 (meaning1479 q) (meaning1527 q) (meaning1542 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1527 = false ∨ valuation q 1542 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) + (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (l₂ := [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1542)) (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82]) (countLit q [-84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) (count1537 q) 4 2 (meaning1480 q) (meaning1526 q) (meaning1542 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1526 = false ∨ valuation q 1542 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1560 = true := by
  have hs : count1549 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27, -28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) + (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82, -84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27, -28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (l₂ := [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82, -84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1560)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27, -28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82, -84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) (count1549 q) 5 7 (meaning1433 q) (meaning1543 q) (meaning1560 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1543 = false ∨ valuation q 1560 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1560 = true := by
  have hs : count1549 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27, -28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) + (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82, -84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27, -28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (l₂ := [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82, -84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1560)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27, -28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82, -84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) (count1549 q) 6 6 (meaning1434 q) (meaning1542 q) (meaning1560 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1542 = false ∨ valuation q 1560 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1560 = true := by
  have hs : count1549 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27, -28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) + (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82, -84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27, -28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (l₂ := [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82, -84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1560)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27, -28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82, -84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) (count1549 q) 7 5 (meaning1435 q) (meaning1541 q) (meaning1560 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1541 = false ∨ valuation q 1560 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1560 = true := by
  have hs : count1549 q = (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27, -28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) + (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82, -84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27, -28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (l₂ := [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82, -84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1560)) (countLit q [-2, -4, -5, -7, -10, -11, -12, -16, -17, -21, -22, -24, -27, -28, -30, -33, -36, -37, -40, -42, -45, -47, -48, -51, -53, -55]) (countLit q [-59, -61, -63, -65, -66, -68, -71, -73, -74, -76, -79, -81, -82, -84, -87, -89, -90, -93, -96, -98, -99, -100, -104, -106, -107, -108]) (count1549 q) 8 4 (meaning1436 q) (meaning1540 q) (meaning1560 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1540 = false ∨ valuation q 1560 = true := counterClause541 (baseVal q)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false := by
  rw [value1560]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1549 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value15, value16, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value17, value20, value26, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (162 : Vertex) (166 : Vertex) (178 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E079.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112079
