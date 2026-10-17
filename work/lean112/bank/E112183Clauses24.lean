import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -109])
  have hm := merge_left (literal (valuationOf q) (1511)) (literal (valuationOf q) (1515)) (countLit q [-104, -106]) (countLit q [-107, -109]) (count1514 q) 2 (meaning1511 q) (meaning1515 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1515 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -106, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1514)) (literal (valuationOf q) (1518)) (countLit q [-98, -99, -101]) (countLit q [-104, -106, -107, -109]) (count1518 q) 1 (meaning1514 q) (meaning1518 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1518 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -106, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1515)) (literal (valuationOf q) (1519)) (countLit q [-98, -99, -101]) (countLit q [-104, -106, -107, -109]) (count1518 q) 2 (meaning1515 q) (meaning1519 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1519 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -106, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1516)) (literal (valuationOf q) (1520)) (countLit q [-98, -99, -101]) (countLit q [-104, -106, -107, -109]) (count1518 q) 3 (meaning1516 q) (meaning1520 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1520 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -106, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1507)) (literal (valuationOf q) (1518)) (countLit q [-98, -99, -101]) (countLit q [-104, -106, -107, -109]) (count1518 q) 1 (meaning1507 q) (meaning1518 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1518 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1519)) (countLit q [-98, -99, -101]) (countLit q [-104, -106, -107, -109]) (count1518 q) 1 1 (meaning1507 q) (meaning1514 q) (meaning1519 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1514 = false ∨ valuation q 1519 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1520)) (countLit q [-98, -99, -101]) (countLit q [-104, -106, -107, -109]) (count1518 q) 1 2 (meaning1507 q) (meaning1515 q) (meaning1520 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1515 = false ∨ valuation q 1520 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -106, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1508)) (literal (valuationOf q) (1519)) (countLit q [-98, -99, -101]) (countLit q [-104, -106, -107, -109]) (count1518 q) 2 (meaning1508 q) (meaning1519 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1519 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -106, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1509)) (literal (valuationOf q) (1520)) (countLit q [-98, -99, -101]) (countLit q [-104, -106, -107, -109]) (count1518 q) 3 (meaning1509 q) (meaning1520 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1520 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1525 = true := by
  have hs : count1525 q = (countLit q [-84, -88, -90, -91, -92, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90, -91, -92, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1518)) (literal (valuationOf q) (1525)) (countLit q [-84, -88, -90, -91, -92, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 1 (meaning1518 q) (meaning1525 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1525 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-84, -88, -90, -91, -92, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90, -91, -92, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1520)) (literal (valuationOf q) (1527)) (countLit q [-84, -88, -90, -91, -92, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 3 (meaning1520 q) (meaning1527 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1527 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-84, -88, -90, -91, -92, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90, -91, -92, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1526)) (countLit q [-84, -88, -90, -91, -92, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 1 1 (meaning1499 q) (meaning1518 q) (meaning1526 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1518 = false ∨ valuation q 1526 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-84, -88, -90, -91, -92, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90, -91, -92, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1527)) (countLit q [-84, -88, -90, -91, -92, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 1 2 (meaning1499 q) (meaning1519 q) (meaning1527 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1519 = false ∨ valuation q 1527 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-84, -88, -90, -91, -92, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90, -91, -92, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1527)) (countLit q [-84, -88, -90, -91, -92, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 2 1 (meaning1500 q) (meaning1518 q) (meaning1527 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1518 = false ∨ valuation q 1527 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1528 = true := by
  have hs : count1525 q = (countLit q [-84, -88, -90, -91, -92, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90, -91, -92, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1528)) (countLit q [-84, -88, -90, -91, -92, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 2 2 (meaning1500 q) (meaning1519 q) (meaning1528 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1519 = false ∨ valuation q 1528 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1529 = true := by
  have hs : count1525 q = (countLit q [-84, -88, -90, -91, -92, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90, -91, -92, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1529)) (countLit q [-84, -88, -90, -91, -92, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 2 3 (meaning1500 q) (meaning1520 q) (meaning1529 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1520 = false ∨ valuation q 1529 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1528 = true := by
  have hs : count1525 q = (countLit q [-84, -88, -90, -91, -92, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90, -91, -92, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1528)) (countLit q [-84, -88, -90, -91, -92, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 3 1 (meaning1501 q) (meaning1518 q) (meaning1528 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1518 = false ∨ valuation q 1528 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1529 = true := by
  have hs : count1525 q = (countLit q [-84, -88, -90, -91, -92, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90, -91, -92, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1529)) (countLit q [-84, -88, -90, -91, -92, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 3 2 (meaning1501 q) (meaning1519 q) (meaning1529 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1519 = false ∨ valuation q 1529 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1530 = true := by
  have hs : count1525 q = (countLit q [-84, -88, -90, -91, -92, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90, -91, -92, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1530)) (countLit q [-84, -88, -90, -91, -92, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 3 3 (meaning1501 q) (meaning1520 q) (meaning1530 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1520 = false ∨ valuation q 1530 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1529 = true := by
  have hs : count1525 q = (countLit q [-84, -88, -90, -91, -92, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90, -91, -92, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1529)) (countLit q [-84, -88, -90, -91, -92, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 4 1 (meaning1502 q) (meaning1518 q) (meaning1529 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1518 = false ∨ valuation q 1529 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1530 = true := by
  have hs : count1525 q = (countLit q [-84, -88, -90, -91, -92, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -88, -90, -91, -92, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1530)) (countLit q [-84, -88, -90, -91, -92, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 4 2 (meaning1502 q) (meaning1519 q) (meaning1530 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1519 = false ∨ valuation q 1530 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1539)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 2 1 (meaning1478 q) (meaning1525 q) (meaning1539 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1525 = false ∨ valuation q 1539 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1540)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 2 2 (meaning1478 q) (meaning1526 q) (meaning1540 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1526 = false ∨ valuation q 1540 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1541)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 2 3 (meaning1478 q) (meaning1527 q) (meaning1541 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1527 = false ∨ valuation q 1541 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1542)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 2 4 (meaning1478 q) (meaning1528 q) (meaning1542 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1528 = false ∨ valuation q 1542 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1543 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1543)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 2 5 (meaning1478 q) (meaning1529 q) (meaning1543 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1529 = false ∨ valuation q 1543 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1544 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1544)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 2 6 (meaning1478 q) (meaning1530 q) (meaning1544 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1530 = false ∨ valuation q 1544 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1540)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 3 1 (meaning1479 q) (meaning1525 q) (meaning1540 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1525 = false ∨ valuation q 1540 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1541)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 3 2 (meaning1479 q) (meaning1526 q) (meaning1541 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1526 = false ∨ valuation q 1541 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1542)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 3 3 (meaning1479 q) (meaning1527 q) (meaning1542 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1527 = false ∨ valuation q 1542 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1543 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1543)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 3 4 (meaning1479 q) (meaning1528 q) (meaning1543 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1528 = false ∨ valuation q 1543 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1544 = true := by
  have hs : count1537 q = (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) + (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (l₂ := [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1544)) (countLit q [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]) (countLit q [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]) (count1537 q) 3 5 (meaning1479 q) (meaning1529 q) (meaning1544 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1529 = false ∨ valuation q 1544 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E183.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112183
