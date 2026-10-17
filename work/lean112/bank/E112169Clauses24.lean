import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1414)) (literal (valuationOf q) (1441)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 1 (meaning1414 q) (meaning1441 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1441 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1442)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 1 1 (meaning1414 q) (meaning1434 q) (meaning1442 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1434 = false ∨ valuation q 1442 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1443)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 1 2 (meaning1414 q) (meaning1435 q) (meaning1443 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1435 = false ∨ valuation q 1443 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1444 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1444)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 1 3 (meaning1414 q) (meaning1436 q) (meaning1444 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1436 = false ∨ valuation q 1444 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1445)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 1 4 (meaning1414 q) (meaning1437 q) (meaning1445 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1437 = false ∨ valuation q 1445 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1415)) (literal (valuationOf q) (1442)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 2 (meaning1415 q) (meaning1442 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1442 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1443)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 2 1 (meaning1415 q) (meaning1434 q) (meaning1443 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1434 = false ∨ valuation q 1443 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1444 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1444)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 2 2 (meaning1415 q) (meaning1435 q) (meaning1444 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1435 = false ∨ valuation q 1444 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1445)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 2 3 (meaning1415 q) (meaning1436 q) (meaning1445 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1436 = false ∨ valuation q 1445 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1446 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1446)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 2 4 (meaning1415 q) (meaning1437 q) (meaning1446 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1437 = false ∨ valuation q 1446 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1447 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1447)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 2 5 (meaning1415 q) (meaning1438 q) (meaning1447 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1438 = false ∨ valuation q 1447 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1448 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1448)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 2 6 (meaning1415 q) (meaning1439 q) (meaning1448 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1439 = false ∨ valuation q 1448 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1416)) (literal (valuationOf q) (1443)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 3 (meaning1416 q) (meaning1443 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1443 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1444 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1444)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 3 1 (meaning1416 q) (meaning1434 q) (meaning1444 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1434 = false ∨ valuation q 1444 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1445)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 3 2 (meaning1416 q) (meaning1435 q) (meaning1445 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1435 = false ∨ valuation q 1445 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1446 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1446)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 3 3 (meaning1416 q) (meaning1436 q) (meaning1446 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1436 = false ∨ valuation q 1446 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1447 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1437)) (literal (valuationOf q) (1447)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 3 4 (meaning1416 q) (meaning1437 q) (meaning1447 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1437 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1437 = false ∨ valuation q 1447 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1448 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1448)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 3 5 (meaning1416 q) (meaning1438 q) (meaning1448 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1438 = false ∨ valuation q 1448 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1444 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1417)) (literal (valuationOf q) (1444)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 4 (meaning1417 q) (meaning1444 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1444 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1445)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 4 1 (meaning1417 q) (meaning1434 q) (meaning1445 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1434 = false ∨ valuation q 1445 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1446 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1446)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 4 2 (meaning1417 q) (meaning1435 q) (meaning1446 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1435 = false ∨ valuation q 1446 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1447 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1447)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 4 3 (meaning1417 q) (meaning1436 q) (meaning1447 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1436 = false ∨ valuation q 1447 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1445 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1418)) (literal (valuationOf q) (1445)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 5 (meaning1418 q) (meaning1445 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1445 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1446 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1446)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 5 1 (meaning1418 q) (meaning1434 q) (meaning1446 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1434 = false ∨ valuation q 1446 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1447 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1447)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 5 2 (meaning1418 q) (meaning1435 q) (meaning1447 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1435 = false ∨ valuation q 1447 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1448 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1448)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 5 3 (meaning1418 q) (meaning1436 q) (meaning1448 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1436 = false ∨ valuation q 1448 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1446 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1419)) (literal (valuationOf q) (1446)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 6 (meaning1419 q) (meaning1446 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1446 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1447 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1447)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 6 1 (meaning1419 q) (meaning1434 q) (meaning1447 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1434 = false ∨ valuation q 1447 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1448 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1448)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 6 2 (meaning1419 q) (meaning1435 q) (meaning1448 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1435 = false ∨ valuation q 1448 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1447 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1420)) (literal (valuationOf q) (1447)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 7 (meaning1420 q) (meaning1447 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1447 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1448 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1420)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1448)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 7 1 (meaning1420 q) (meaning1434 q) (meaning1448 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1434 = false ∨ valuation q 1448 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1455 = true := by
  have hs : count1455 q = (countLit q [-31]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1455)) (countLit q [-31]) (countLit q [-35]) (count1455 q) 1 (meaningNeg35 q) (meaning1455 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1455 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E169.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112169
