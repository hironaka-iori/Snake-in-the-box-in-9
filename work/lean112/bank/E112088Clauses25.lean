import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_left (literal (valuationOf q) (1441)) (literal (valuationOf q) (1452)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 1 (meaning1441 q) (meaning1452 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1452 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1453)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 1 1 (meaning1441 q) (meaning1448 q) (meaning1453 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1448 = false ∨ valuation q 1453 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1454)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 1 2 (meaning1441 q) (meaning1449 q) (meaning1454 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1449 = false ∨ valuation q 1454 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1455)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 1 3 (meaning1441 q) (meaning1450 q) (meaning1455 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1450 = false ∨ valuation q 1455 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1456 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1456)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 1 4 (meaning1441 q) (meaning1451 q) (meaning1456 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1451 = false ∨ valuation q 1456 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_left (literal (valuationOf q) (1442)) (literal (valuationOf q) (1453)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 2 (meaning1442 q) (meaning1453 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1453 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1454)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 2 1 (meaning1442 q) (meaning1448 q) (meaning1454 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1448 = false ∨ valuation q 1454 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1455)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 2 2 (meaning1442 q) (meaning1449 q) (meaning1455 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1449 = false ∨ valuation q 1455 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1456 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1456)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 2 3 (meaning1442 q) (meaning1450 q) (meaning1456 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1450 = false ∨ valuation q 1456 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1457 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1457)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 2 4 (meaning1442 q) (meaning1451 q) (meaning1457 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1451 = false ∨ valuation q 1457 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_left (literal (valuationOf q) (1443)) (literal (valuationOf q) (1454)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 3 (meaning1443 q) (meaning1454 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1454 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1455)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 3 1 (meaning1443 q) (meaning1448 q) (meaning1455 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1448 = false ∨ valuation q 1455 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1456 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1456)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 3 2 (meaning1443 q) (meaning1449 q) (meaning1456 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1449 = false ∨ valuation q 1456 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1457 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1457)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 3 3 (meaning1443 q) (meaning1450 q) (meaning1457 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1450 = false ∨ valuation q 1457 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1458 = true := by
  have hs : count1452 q = (countLit q [-29, -32, -33]) + (countLit q [-35, -36, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33]) (l₂ := [-35, -36, -39, -40])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1458)) (countLit q [-29, -32, -33]) (countLit q [-35, -36, -39, -40]) (count1452 q) 3 4 (meaning1443 q) (meaning1451 q) (meaning1458 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1451 = false ∨ valuation q 1458 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1459)) (countLit q [-42]) (countLit q [-45]) (count1459 q) 1 (meaningNeg45 q) (meaning1459 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1459 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1459)) (countLit q [-42]) (countLit q [-45]) (count1459 q) 1 (meaningNeg42 q) (meaning1459 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1459 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 45 = true ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (1460)) (countLit q [-42]) (countLit q [-45]) (count1459 q) 1 1 (meaningNeg42 q) (meaningNeg45 q) (meaning1460 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 45 = true ∨ valuation q 1460 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1461 = true := by
  have hs : count1461 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1461)) (countLit q [-47]) (countLit q [-48]) (count1461 q) 1 (meaningNeg48 q) (meaning1461 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1461 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1461 = true := by
  have hs : count1461 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1461)) (countLit q [-47]) (countLit q [-48]) (count1461 q) 1 (meaningNeg47 q) (meaning1461 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1461 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 48 = true ∨ valuationOf q 1462 = true := by
  have hs : count1461 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (1462)) (countLit q [-47]) (countLit q [-48]) (count1461 q) 1 1 (meaningNeg47 q) (meaningNeg48 q) (meaning1462 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 48 = true ∨ valuation q 1462 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_right (literal (valuationOf q) (1461)) (literal (valuationOf q) (1463)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1463 q) 1 (meaning1461 q) (meaning1463 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1463 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1464 = true := by
  have hs : count1463 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_right (literal (valuationOf q) (1462)) (literal (valuationOf q) (1464)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1463 q) 2 (meaning1462 q) (meaning1464 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1464 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_left (literal (valuationOf q) (1459)) (literal (valuationOf q) (1463)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1463 q) 1 (meaning1459 q) (meaning1463 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1463 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1464 = true := by
  have hs : count1463 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1464)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1463 q) 1 1 (meaning1459 q) (meaning1461 q) (meaning1464 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1461 = false ∨ valuation q 1464 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1465 = true := by
  have hs : count1463 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1465)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1463 q) 1 2 (meaning1459 q) (meaning1462 q) (meaning1465 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1462 = false ∨ valuation q 1465 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1464 = true := by
  have hs : count1463 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1464)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1463 q) 2 (meaning1460 q) (meaning1464 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1464 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1465 = true := by
  have hs : count1463 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1465)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1463 q) 2 1 (meaning1460 q) (meaning1461 q) (meaning1465 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1461 = false ∨ valuation q 1465 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1466 = true := by
  have hs : count1463 q = (countLit q [-42, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-42, -45]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1466)) (countLit q [-42, -45]) (countLit q [-47, -48]) (count1463 q) 2 2 (meaning1460 q) (meaning1462 q) (meaning1466 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1462 = false ∨ valuation q 1466 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-51]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (1467)) (countLit q [-51]) (countLit q [-55]) (count1467 q) 1 (meaningNeg55 q) (meaning1467 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1467 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 55 = true ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-51]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (1468)) (countLit q [-51]) (countLit q [-55]) (count1467 q) 1 1 (meaningNeg51 q) (meaningNeg55 q) (meaning1468 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 55 = true ∨ valuation q 1468 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1469)) (countLit q [-56]) (countLit q [-57]) (count1469 q) 1 (meaningNeg57 q) (meaning1469 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1469 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E088.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112088
