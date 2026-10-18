import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1438 = true := by
  have hs : count1436 q = (countLit q [-36, -39]) + (countLit q [-40, -43]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -43])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1438)) (countLit q [-36, -39]) (countLit q [-40, -43]) (count1436 q) 2 1 (meaning1433 q) (meaning1434 q) (meaning1438 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1434 = false ∨ valuation q 1438 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1439 = true := by
  have hs : count1436 q = (countLit q [-36, -39]) + (countLit q [-40, -43]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -43])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1439)) (countLit q [-36, -39]) (countLit q [-40, -43]) (count1436 q) 2 2 (meaning1433 q) (meaning1435 q) (meaning1439 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1435 = false ∨ valuation q 1439 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1440 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_right (literal (valuationOf q) (1436)) (literal (valuationOf q) (1440)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 1 (meaning1436 q) (meaning1440 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1440 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1441 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_right (literal (valuationOf q) (1437)) (literal (valuationOf q) (1441)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 2 (meaning1437 q) (meaning1441 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1441 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1442 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_right (literal (valuationOf q) (1438)) (literal (valuationOf q) (1442)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 3 (meaning1438 q) (meaning1442 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1442 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1443 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_right (literal (valuationOf q) (1439)) (literal (valuationOf q) (1443)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 4 (meaning1439 q) (meaning1443 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1443 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1440 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_left (literal (valuationOf q) (1429)) (literal (valuationOf q) (1440)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 1 (meaning1429 q) (meaning1440 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1440 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1441 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1441)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 1 1 (meaning1429 q) (meaning1436 q) (meaning1441 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1436 = false ∨ valuation q 1441 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1442 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1442)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 1 2 (meaning1429 q) (meaning1437 q) (meaning1442 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1437 = false ∨ valuation q 1442 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1443 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1443)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 1 3 (meaning1429 q) (meaning1438 q) (meaning1443 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1438 = false ∨ valuation q 1443 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1441 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_left (literal (valuationOf q) (1430)) (literal (valuationOf q) (1441)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 2 (meaning1430 q) (meaning1441 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1441 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1442 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1442)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 2 1 (meaning1430 q) (meaning1436 q) (meaning1442 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1436 = false ∨ valuation q 1442 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1443 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1443)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 2 2 (meaning1430 q) (meaning1437 q) (meaning1443 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1437 = false ∨ valuation q 1443 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1442 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_left (literal (valuationOf q) (1431)) (literal (valuationOf q) (1442)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 3 (meaning1431 q) (meaning1442 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1442 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1443 = true := by
  have hs : count1440 q = (countLit q [-30, -31, -34]) + (countLit q [-36, -39, -40, -43]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -34]) (l₂ := [-36, -39, -40, -43])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1443)) (countLit q [-30, -31, -34]) (countLit q [-36, -39, -40, -43]) (count1440 q) 3 1 (meaning1431 q) (meaning1436 q) (meaning1443 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1436 = false ∨ valuation q 1443 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1447 = true := by
  have hs : count1447 q = (countLit q [-47]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1447)) (countLit q [-47]) (countLit q [-51]) (count1447 q) 1 (meaningNeg51 q) (meaning1447 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1447 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1447 = true := by
  have hs : count1447 q = (countLit q [-47]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1447)) (countLit q [-47]) (countLit q [-51]) (count1447 q) 1 (meaningNeg47 q) (meaning1447 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1447 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1448 = true := by
  have hs : count1447 q = (countLit q [-47]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1448)) (countLit q [-47]) (countLit q [-51]) (count1447 q) 1 1 (meaningNeg47 q) (meaningNeg51 q) (meaning1448 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 51 = true ∨ valuation q 1448 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1449 = true := by
  have hs : count1449 q = (countLit q [-44]) + (countLit q [-47, -51]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-47, -51])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1449)) (countLit q [-44]) (countLit q [-47, -51]) (count1449 q) 1 (meaning1447 q) (meaning1449 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1449 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-44]) + (countLit q [-47, -51]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-47, -51])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1450)) (countLit q [-44]) (countLit q [-47, -51]) (count1449 q) 2 (meaning1448 q) (meaning1450 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1450 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1449 = true := by
  have hs : count1449 q = (countLit q [-44]) + (countLit q [-47, -51]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-47, -51])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1449)) (countLit q [-44]) (countLit q [-47, -51]) (count1449 q) 1 (meaningNeg44 q) (meaning1449 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1449 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-44]) + (countLit q [-47, -51]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-47, -51])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1450)) (countLit q [-44]) (countLit q [-47, -51]) (count1449 q) 1 1 (meaningNeg44 q) (meaning1447 q) (meaning1450 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1447 = false ∨ valuation q 1450 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1448 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-44]) + (countLit q [-47, -51]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-47, -51])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1451)) (countLit q [-44]) (countLit q [-47, -51]) (count1449 q) 1 2 (meaningNeg44 q) (meaning1448 q) (meaning1451 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1448 = false ∨ valuation q 1451 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1452)) (countLit q [-52]) (countLit q [-54]) (count1452 q) 1 (meaningNeg54 q) (meaning1452 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1452 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1452)) (countLit q [-52]) (countLit q [-54]) (count1452 q) 1 (meaningNeg52 q) (meaning1452 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1452 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1453)) (countLit q [-52]) (countLit q [-54]) (count1452 q) 1 1 (meaningNeg52 q) (meaningNeg54 q) (meaning1453 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 1453 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-57]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1454)) (countLit q [-57]) (countLit q [-58]) (count1454 q) 1 (meaningNeg58 q) (meaning1454 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1454 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-57]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (1454)) (countLit q [-57]) (countLit q [-58]) (count1454 q) 1 (meaningNeg57 q) (meaning1454 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1454 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 58 = true ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-57]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (-58)) (literal (valuationOf q) (1455)) (countLit q [-57]) (countLit q [-58]) (count1454 q) 1 1 (meaningNeg57 q) (meaningNeg58 q) (meaning1455 q) hs
  change (! (valuationOf q 57)) = false ∨ (! (valuationOf q 58)) = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 58 = true ∨ valuation q 1455 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-52, -54]) + (countLit q [-57, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-57, -58])
  have hm := merge_right (literal (valuationOf q) (1454)) (literal (valuationOf q) (1456)) (countLit q [-52, -54]) (countLit q [-57, -58]) (count1456 q) 1 (meaning1454 q) (meaning1456 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1456 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-52, -54]) + (countLit q [-57, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-57, -58])
  have hm := merge_right (literal (valuationOf q) (1455)) (literal (valuationOf q) (1457)) (countLit q [-52, -54]) (countLit q [-57, -58]) (count1456 q) 2 (meaning1455 q) (meaning1457 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1457 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-52, -54]) + (countLit q [-57, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-57, -58])
  have hm := merge_left (literal (valuationOf q) (1452)) (literal (valuationOf q) (1456)) (countLit q [-52, -54]) (countLit q [-57, -58]) (count1456 q) 1 (meaning1452 q) (meaning1456 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1456 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E168.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112168
