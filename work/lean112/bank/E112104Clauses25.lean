import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-14, -17, -19, -21]) + (countLit q [-23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -21]) (l₂ := [-23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1453)) (countLit q [-14, -17, -19, -21]) (countLit q [-23, -24, -25, -28]) (count1449 q) 1 4 (meaning1437 q) (meaning1448 q) (meaning1453 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1448 = false ∨ valuation q 1453 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-14, -17, -19, -21]) + (countLit q [-23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -21]) (l₂ := [-23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1451)) (countLit q [-14, -17, -19, -21]) (countLit q [-23, -24, -25, -28]) (count1449 q) 2 1 (meaning1438 q) (meaning1445 q) (meaning1451 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1445 = false ∨ valuation q 1451 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-14, -17, -19, -21]) + (countLit q [-23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -21]) (l₂ := [-23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1452)) (countLit q [-14, -17, -19, -21]) (countLit q [-23, -24, -25, -28]) (count1449 q) 2 2 (meaning1438 q) (meaning1446 q) (meaning1452 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1446 = false ∨ valuation q 1452 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-14, -17, -19, -21]) + (countLit q [-23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -21]) (l₂ := [-23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1453)) (countLit q [-14, -17, -19, -21]) (countLit q [-23, -24, -25, -28]) (count1449 q) 2 3 (meaning1438 q) (meaning1447 q) (meaning1453 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1447 = false ∨ valuation q 1453 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-14, -17, -19, -21]) + (countLit q [-23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -21]) (l₂ := [-23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1452)) (countLit q [-14, -17, -19, -21]) (countLit q [-23, -24, -25, -28]) (count1449 q) 3 1 (meaning1439 q) (meaning1445 q) (meaning1452 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1445 = false ∨ valuation q 1452 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-14, -17, -19, -21]) + (countLit q [-23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -21]) (l₂ := [-23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1453)) (countLit q [-14, -17, -19, -21]) (countLit q [-23, -24, -25, -28]) (count1449 q) 3 2 (meaning1439 q) (meaning1446 q) (meaning1453 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1446 = false ∨ valuation q 1453 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1454 = true := by
  have hs : count1449 q = (countLit q [-14, -17, -19, -21]) + (countLit q [-23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -21]) (l₂ := [-23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1454)) (countLit q [-14, -17, -19, -21]) (countLit q [-23, -24, -25, -28]) (count1449 q) 3 3 (meaning1439 q) (meaning1447 q) (meaning1454 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1447 = false ∨ valuation q 1454 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-14, -17, -19, -21]) + (countLit q [-23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -21]) (l₂ := [-23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1440)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1453)) (countLit q [-14, -17, -19, -21]) (countLit q [-23, -24, -25, -28]) (count1449 q) 4 1 (meaning1440 q) (meaning1445 q) (meaning1453 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1445 = false ∨ valuation q 1453 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1454 = true := by
  have hs : count1449 q = (countLit q [-14, -17, -19, -21]) + (countLit q [-23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -21]) (l₂ := [-23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1440)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1454)) (countLit q [-14, -17, -19, -21]) (countLit q [-23, -24, -25, -28]) (count1449 q) 4 2 (meaning1440 q) (meaning1446 q) (meaning1454 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1446 = false ∨ valuation q 1454 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1461 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1461)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 2 3 (meaning1427 q) (meaning1451 q) (meaning1461 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1451 = false ∨ valuation q 1461 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1462 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1462)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 2 4 (meaning1427 q) (meaning1452 q) (meaning1462 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1452 = false ∨ valuation q 1462 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1463 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1463)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 2 5 (meaning1427 q) (meaning1453 q) (meaning1463 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1453 = false ∨ valuation q 1463 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1464 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 2 6 (meaning1427 q) (meaning1454 q) (meaning1464 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1454 = false ∨ valuation q 1464 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1461 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1461)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 3 2 (meaning1428 q) (meaning1450 q) (meaning1461 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1450 = false ∨ valuation q 1461 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1462 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1462)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 3 3 (meaning1428 q) (meaning1451 q) (meaning1462 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1451 = false ∨ valuation q 1462 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1463 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1463)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 3 4 (meaning1428 q) (meaning1452 q) (meaning1463 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1452 = false ∨ valuation q 1463 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1464 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 3 5 (meaning1428 q) (meaning1453 q) (meaning1464 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1453 = false ∨ valuation q 1464 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1465 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1465)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 3 6 (meaning1428 q) (meaning1454 q) (meaning1465 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1454 = false ∨ valuation q 1465 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1462 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1462)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 4 2 (meaning1429 q) (meaning1450 q) (meaning1462 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1450 = false ∨ valuation q 1462 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1463 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1463)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 4 3 (meaning1429 q) (meaning1451 q) (meaning1463 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1451 = false ∨ valuation q 1463 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1464 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 4 4 (meaning1429 q) (meaning1452 q) (meaning1464 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1452 = false ∨ valuation q 1464 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1464 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 5 3 (meaning1430 q) (meaning1451 q) (meaning1464 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1451 = false ∨ valuation q 1464 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1464 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -8, -9, -13]) + (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -8, -9, -13]) (l₂ := [-14, -17, -19, -21, -23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5, -6, -8, -9, -13]) (countLit q [-14, -17, -19, -21, -23, -24, -25, -28]) (count1457 q) 6 2 (meaning1431 q) (meaning1450 q) (meaning1464 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1450 = false ∨ valuation q 1464 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1472)) (countLit q [-34]) (countLit q [-35]) (count1472 q) 1 (meaningNeg35 q) (meaning1472 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1472 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1472)) (countLit q [-34]) (countLit q [-35]) (count1472 q) 1 (meaningNeg34 q) (meaning1472 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1472 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1473)) (countLit q [-34]) (countLit q [-35]) (count1472 q) 1 1 (meaningNeg34 q) (meaningNeg35 q) (meaning1473 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 35 = true ∨ valuation q 1473 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-31]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (countLit q [-31]) (countLit q [-34, -35]) (count1474 q) 1 (meaning1472 q) (meaning1474 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-31]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1473)) (literal (valuationOf q) (1475)) (countLit q [-31]) (countLit q [-34, -35]) (count1474 q) 2 (meaning1473 q) (meaning1475 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1475 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-31]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34, -35])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1474)) (countLit q [-31]) (countLit q [-34, -35]) (count1474 q) 1 (meaningNeg31 q) (meaning1474 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1474 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-31]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34, -35])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1475)) (countLit q [-31]) (countLit q [-34, -35]) (count1474 q) 1 1 (meaningNeg31 q) (meaning1472 q) (meaning1475 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1472 = false ∨ valuation q 1475 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1473 = false ∨ valuationOf q 1476 = true := by
  have hs : count1474 q = (countLit q [-31]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34, -35])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1476)) (countLit q [-31]) (countLit q [-34, -35]) (count1474 q) 1 2 (meaningNeg31 q) (meaning1473 q) (meaning1476 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1473 = false ∨ valuation q 1476 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-36]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (1477)) (countLit q [-36]) (countLit q [-39]) (count1477 q) 1 (meaningNeg39 q) (meaning1477 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1477 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E104.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112104
