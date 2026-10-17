import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1430 = true := by
  have hs : count1426 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1430)) (countLit q [-2, -4, -5]) (countLit q [-6, -9, -11, -13]) (count1426 q) 3 2 (meaning1417 q) (meaning1423 q) (meaning1430 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1423 = false ∨ valuation q 1430 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1431 = true := by
  have hs : count1426 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -9, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -9, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1424)) (literal (valuationOf q) (1431)) (countLit q [-2, -4, -5]) (countLit q [-6, -9, -11, -13]) (count1426 q) 3 3 (meaning1417 q) (meaning1424 q) (meaning1431 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1424 = false ∨ valuation q 1431 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-14]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16])
  have hm := merge_right (literal (valuationOf q) (-16)) (literal (valuationOf q) (1433)) (countLit q [-14]) (countLit q [-16]) (count1433 q) 1 (meaningNeg16 q) (meaning1433 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1433 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-14]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1433)) (countLit q [-14]) (countLit q [-16]) (count1433 q) 1 (meaningNeg14 q) (meaning1433 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1433 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 16 = true ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-14]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-16)) (literal (valuationOf q) (1434)) (countLit q [-14]) (countLit q [-16]) (count1433 q) 1 1 (meaningNeg14 q) (meaningNeg16 q) (meaning1434 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 16)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 16 = true ∨ valuation q 1434 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1435 = true := by
  have hs : count1435 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1435)) (countLit q [-19]) (countLit q [-20]) (count1435 q) 1 (meaningNeg20 q) (meaning1435 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1435 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1435 = true := by
  have hs : count1435 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1435)) (countLit q [-19]) (countLit q [-20]) (count1435 q) 1 (meaningNeg19 q) (meaning1435 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1435 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 20 = true ∨ valuationOf q 1436 = true := by
  have hs : count1435 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (1436)) (countLit q [-19]) (countLit q [-20]) (count1435 q) 1 1 (meaningNeg19 q) (meaningNeg20 q) (meaning1436 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 20 = true ∨ valuation q 1436 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-14, -16]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -16]) (l₂ := [-19, -20])
  have hm := merge_right (literal (valuationOf q) (1435)) (literal (valuationOf q) (1437)) (countLit q [-14, -16]) (countLit q [-19, -20]) (count1437 q) 1 (meaning1435 q) (meaning1437 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1437 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1438 = true := by
  have hs : count1437 q = (countLit q [-14, -16]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -16]) (l₂ := [-19, -20])
  have hm := merge_right (literal (valuationOf q) (1436)) (literal (valuationOf q) (1438)) (countLit q [-14, -16]) (countLit q [-19, -20]) (count1437 q) 2 (meaning1436 q) (meaning1438 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1438 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-14, -16]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -16]) (l₂ := [-19, -20])
  have hm := merge_left (literal (valuationOf q) (1433)) (literal (valuationOf q) (1437)) (countLit q [-14, -16]) (countLit q [-19, -20]) (count1437 q) 1 (meaning1433 q) (meaning1437 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1437 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1438 = true := by
  have hs : count1437 q = (countLit q [-14, -16]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -16]) (l₂ := [-19, -20])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1438)) (countLit q [-14, -16]) (countLit q [-19, -20]) (count1437 q) 1 1 (meaning1433 q) (meaning1435 q) (meaning1438 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1435 = false ∨ valuation q 1438 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1439 = true := by
  have hs : count1437 q = (countLit q [-14, -16]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -16]) (l₂ := [-19, -20])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1439)) (countLit q [-14, -16]) (countLit q [-19, -20]) (count1437 q) 1 2 (meaning1433 q) (meaning1436 q) (meaning1439 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1436 = false ∨ valuation q 1439 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1438 = true := by
  have hs : count1437 q = (countLit q [-14, -16]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -16]) (l₂ := [-19, -20])
  have hm := merge_left (literal (valuationOf q) (1434)) (literal (valuationOf q) (1438)) (countLit q [-14, -16]) (countLit q [-19, -20]) (count1437 q) 2 (meaning1434 q) (meaning1438 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1438 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1439 = true := by
  have hs : count1437 q = (countLit q [-14, -16]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-14, -16]) (l₂ := [-19, -20])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1439)) (countLit q [-14, -16]) (countLit q [-19, -20]) (count1437 q) 2 1 (meaning1434 q) (meaning1435 q) (meaning1439 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1435 = false ∨ valuation q 1439 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1441)) (countLit q [-22]) (countLit q [-25]) (count1441 q) 1 (meaningNeg25 q) (meaning1441 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1441 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1441)) (countLit q [-22]) (countLit q [-25]) (count1441 q) 1 (meaningNeg22 q) (meaning1441 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1441 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 25 = true ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (1442)) (countLit q [-22]) (countLit q [-25]) (count1441 q) 1 1 (meaningNeg22 q) (meaningNeg25 q) (meaning1442 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 25 = true ∨ valuation q 1442 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1443)) (countLit q [-27]) (countLit q [-29]) (count1443 q) 1 (meaningNeg29 q) (meaning1443 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1443 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1443)) (countLit q [-27]) (countLit q [-29]) (count1443 q) 1 (meaningNeg27 q) (meaning1443 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1443 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 29 = true ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (-29)) (literal (valuationOf q) (1444)) (countLit q [-27]) (countLit q [-29]) (count1443 q) 1 1 (meaningNeg27 q) (meaningNeg29 q) (meaning1444 q) hs
  change (! (valuationOf q 27)) = false ∨ (! (valuationOf q 29)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 1444 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-22, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (1443)) (literal (valuationOf q) (1445)) (countLit q [-22, -25]) (countLit q [-27, -29]) (count1445 q) 1 (meaning1443 q) (meaning1445 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1445 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-22, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (1444)) (literal (valuationOf q) (1446)) (countLit q [-22, -25]) (countLit q [-27, -29]) (count1445 q) 2 (meaning1444 q) (meaning1446 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1446 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-22, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (1441)) (literal (valuationOf q) (1445)) (countLit q [-22, -25]) (countLit q [-27, -29]) (count1445 q) 1 (meaning1441 q) (meaning1445 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1445 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-22, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1446)) (countLit q [-22, -25]) (countLit q [-27, -29]) (count1445 q) 1 1 (meaning1441 q) (meaning1443 q) (meaning1446 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1443 = false ∨ valuation q 1446 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1447 = true := by
  have hs : count1445 q = (countLit q [-22, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1447)) (countLit q [-22, -25]) (countLit q [-27, -29]) (count1445 q) 1 2 (meaning1441 q) (meaning1444 q) (meaning1447 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1444 = false ∨ valuation q 1447 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-22, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (1442)) (literal (valuationOf q) (1446)) (countLit q [-22, -25]) (countLit q [-27, -29]) (count1445 q) 2 (meaning1442 q) (meaning1446 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1446 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1447 = true := by
  have hs : count1445 q = (countLit q [-22, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1447)) (countLit q [-22, -25]) (countLit q [-27, -29]) (count1445 q) 2 1 (meaning1442 q) (meaning1443 q) (meaning1447 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1443 = false ∨ valuation q 1447 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1448 = true := by
  have hs : count1445 q = (countLit q [-22, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1448)) (countLit q [-22, -25]) (countLit q [-27, -29]) (count1445 q) 2 2 (meaning1442 q) (meaning1444 q) (meaning1448 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1444 = false ∨ valuation q 1448 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1449 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_right (literal (valuationOf q) (1445)) (literal (valuationOf q) (1449)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 1 (meaning1445 q) (meaning1449 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1449 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1450)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 2 (meaning1446 q) (meaning1450 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1450 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_right (literal (valuationOf q) (1447)) (literal (valuationOf q) (1451)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 3 (meaning1447 q) (meaning1451 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1451 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E110.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112110
