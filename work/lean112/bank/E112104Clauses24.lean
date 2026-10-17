import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1429 = true := by
  have hs : count1426 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -8, -9, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -8, -9, -13])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1429)) (countLit q [-2, -4, -5]) (countLit q [-6, -8, -9, -13]) (count1426 q) 3 1 (meaning1417 q) (meaning1422 q) (meaning1429 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1422 = false ∨ valuation q 1429 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1431 = true := by
  have hs : count1426 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -8, -9, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -8, -9, -13])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1424)) (literal (valuationOf q) (1431)) (countLit q [-2, -4, -5]) (countLit q [-6, -8, -9, -13]) (count1426 q) 3 3 (meaning1417 q) (meaning1424 q) (meaning1431 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1424 = false ∨ valuation q 1431 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (1433)) (countLit q [-14]) (countLit q [-17]) (count1433 q) 1 (meaningNeg17 q) (meaning1433 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1433 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1433)) (countLit q [-14]) (countLit q [-17]) (count1433 q) 1 (meaningNeg14 q) (meaning1433 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1433 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 17 = true ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-14]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-17])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-17)) (literal (valuationOf q) (1434)) (countLit q [-14]) (countLit q [-17]) (count1433 q) 1 1 (meaningNeg14 q) (meaningNeg17 q) (meaning1434 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 17)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 17 = true ∨ valuation q 1434 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1435 = true := by
  have hs : count1435 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1435)) (countLit q [-19]) (countLit q [-21]) (count1435 q) 1 (meaningNeg21 q) (meaning1435 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1435 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1435 = true := by
  have hs : count1435 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1435)) (countLit q [-19]) (countLit q [-21]) (count1435 q) 1 (meaningNeg19 q) (meaning1435 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1435 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 21 = true ∨ valuationOf q 1436 = true := by
  have hs : count1435 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (1436)) (countLit q [-19]) (countLit q [-21]) (count1435 q) 1 1 (meaningNeg19 q) (meaningNeg21 q) (meaning1436 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 1436 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-14, -17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuationOf q) (1435)) (literal (valuationOf q) (1437)) (countLit q [-14, -17]) (countLit q [-19, -21]) (count1437 q) 1 (meaning1435 q) (meaning1437 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1437 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1438 = true := by
  have hs : count1437 q = (countLit q [-14, -17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuationOf q) (1436)) (literal (valuationOf q) (1438)) (countLit q [-14, -17]) (countLit q [-19, -21]) (count1437 q) 2 (meaning1436 q) (meaning1438 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1438 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-14, -17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -21])
  have hm := merge_left (literal (valuationOf q) (1433)) (literal (valuationOf q) (1437)) (countLit q [-14, -17]) (countLit q [-19, -21]) (count1437 q) 1 (meaning1433 q) (meaning1437 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1437 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1438 = true := by
  have hs : count1437 q = (countLit q [-14, -17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1438)) (countLit q [-14, -17]) (countLit q [-19, -21]) (count1437 q) 1 1 (meaning1433 q) (meaning1435 q) (meaning1438 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1435 = false ∨ valuation q 1438 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1439 = true := by
  have hs : count1437 q = (countLit q [-14, -17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1439)) (countLit q [-14, -17]) (countLit q [-19, -21]) (count1437 q) 1 2 (meaning1433 q) (meaning1436 q) (meaning1439 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1436 = false ∨ valuation q 1439 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1438 = true := by
  have hs : count1437 q = (countLit q [-14, -17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -21])
  have hm := merge_left (literal (valuationOf q) (1434)) (literal (valuationOf q) (1438)) (countLit q [-14, -17]) (countLit q [-19, -21]) (count1437 q) 2 (meaning1434 q) (meaning1438 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1438 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1439 = true := by
  have hs : count1437 q = (countLit q [-14, -17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1439)) (countLit q [-14, -17]) (countLit q [-19, -21]) (count1437 q) 2 1 (meaning1434 q) (meaning1435 q) (meaning1439 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1435 = false ∨ valuation q 1439 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1440 = true := by
  have hs : count1437 q = (countLit q [-14, -17]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -17]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1440)) (countLit q [-14, -17]) (countLit q [-19, -21]) (count1437 q) 2 2 (meaning1434 q) (meaning1436 q) (meaning1440 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1436 = false ∨ valuation q 1440 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1441)) (countLit q [-23]) (countLit q [-24]) (count1441 q) 1 (meaningNeg24 q) (meaning1441 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1441 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (1441)) (countLit q [-23]) (countLit q [-24]) (count1441 q) 1 (meaningNeg23 q) (meaning1441 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1441 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-23)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1442)) (countLit q [-23]) (countLit q [-24]) (count1441 q) 1 1 (meaningNeg23 q) (meaningNeg24 q) (meaning1442 q) hs
  change (! (valuationOf q 23)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 24 = true ∨ valuation q 1442 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-25]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-28])
  have hm := merge_right (literal (valuationOf q) (-28)) (literal (valuationOf q) (1443)) (countLit q [-25]) (countLit q [-28]) (count1443 q) 1 (meaningNeg28 q) (meaning1443 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1443 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-25]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1443)) (countLit q [-25]) (countLit q [-28]) (count1443 q) 1 (meaningNeg25 q) (meaning1443 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1443 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 28 = true ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-25]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-28])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-28)) (literal (valuationOf q) (1444)) (countLit q [-25]) (countLit q [-28]) (count1443 q) 1 1 (meaningNeg25 q) (meaningNeg28 q) (meaning1444 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 28)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 28 = true ∨ valuation q 1444 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-23, -24]) + (countLit q [-25, -28]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-25, -28])
  have hm := merge_right (literal (valuationOf q) (1443)) (literal (valuationOf q) (1445)) (countLit q [-23, -24]) (countLit q [-25, -28]) (count1445 q) 1 (meaning1443 q) (meaning1445 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1445 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-23, -24]) + (countLit q [-25, -28]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-25, -28])
  have hm := merge_right (literal (valuationOf q) (1444)) (literal (valuationOf q) (1446)) (countLit q [-23, -24]) (countLit q [-25, -28]) (count1445 q) 2 (meaning1444 q) (meaning1446 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1446 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-23, -24]) + (countLit q [-25, -28]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-25, -28])
  have hm := merge_left (literal (valuationOf q) (1441)) (literal (valuationOf q) (1445)) (countLit q [-23, -24]) (countLit q [-25, -28]) (count1445 q) 1 (meaning1441 q) (meaning1445 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1445 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-23, -24]) + (countLit q [-25, -28]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-25, -28])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1446)) (countLit q [-23, -24]) (countLit q [-25, -28]) (count1445 q) 1 1 (meaning1441 q) (meaning1443 q) (meaning1446 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1443 = false ∨ valuation q 1446 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-23, -24]) + (countLit q [-25, -28]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-25, -28])
  have hm := merge_left (literal (valuationOf q) (1442)) (literal (valuationOf q) (1446)) (countLit q [-23, -24]) (countLit q [-25, -28]) (count1445 q) 2 (meaning1442 q) (meaning1446 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1446 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1447 = true := by
  have hs : count1445 q = (countLit q [-23, -24]) + (countLit q [-25, -28]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-25, -28])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1447)) (countLit q [-23, -24]) (countLit q [-25, -28]) (count1445 q) 2 1 (meaning1442 q) (meaning1443 q) (meaning1447 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1443 = false ∨ valuation q 1447 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1448 = true := by
  have hs : count1445 q = (countLit q [-23, -24]) + (countLit q [-25, -28]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-25, -28])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1444)) (literal (valuationOf q) (1448)) (countLit q [-23, -24]) (countLit q [-25, -28]) (count1445 q) 2 2 (meaning1442 q) (meaning1444 q) (meaning1448 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1444 = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1444 = false ∨ valuation q 1448 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-14, -17, -19, -21]) + (countLit q [-23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -21]) (l₂ := [-23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1450)) (countLit q [-14, -17, -19, -21]) (countLit q [-23, -24, -25, -28]) (count1449 q) 1 1 (meaning1437 q) (meaning1445 q) (meaning1450 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1445 = false ∨ valuation q 1450 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-14, -17, -19, -21]) + (countLit q [-23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -21]) (l₂ := [-23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1451)) (countLit q [-14, -17, -19, -21]) (countLit q [-23, -24, -25, -28]) (count1449 q) 1 2 (meaning1437 q) (meaning1446 q) (meaning1451 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1446 = false ∨ valuation q 1451 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-14, -17, -19, -21]) + (countLit q [-23, -24, -25, -28]) := List.countP_append (p := literal q) (l₁ := [-14, -17, -19, -21]) (l₂ := [-23, -24, -25, -28])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1452)) (countLit q [-14, -17, -19, -21]) (countLit q [-23, -24, -25, -28]) (count1449 q) 1 3 (meaning1437 q) (meaning1447 q) (meaning1452 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1447 = false ∨ valuation q 1452 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E104.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112104
