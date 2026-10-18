import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1449 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1437)) (literal (valuationOf q) (1449)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 1 (meaning1437 q) (meaning1449 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1449 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1450)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 1 1 (meaning1437 q) (meaning1445 q) (meaning1450 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1445 = false ∨ valuation q 1450 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1451)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 1 2 (meaning1437 q) (meaning1446 q) (meaning1451 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1446 = false ∨ valuation q 1451 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1452)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 1 3 (meaning1437 q) (meaning1447 q) (meaning1452 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1447 = false ∨ valuation q 1452 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1453)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 1 4 (meaning1437 q) (meaning1448 q) (meaning1453 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1448 = false ∨ valuation q 1453 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1438)) (literal (valuationOf q) (1450)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 2 (meaning1438 q) (meaning1450 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1450 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1451)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 2 1 (meaning1438 q) (meaning1445 q) (meaning1451 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1445 = false ∨ valuation q 1451 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1452)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 2 2 (meaning1438 q) (meaning1446 q) (meaning1452 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1446 = false ∨ valuation q 1452 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1453)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 2 3 (meaning1438 q) (meaning1447 q) (meaning1453 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1447 = false ∨ valuation q 1453 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1454 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1454)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 2 4 (meaning1438 q) (meaning1448 q) (meaning1454 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1448 = false ∨ valuation q 1454 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1439)) (literal (valuationOf q) (1451)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 3 (meaning1439 q) (meaning1451 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1451 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1452)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 3 1 (meaning1439 q) (meaning1445 q) (meaning1452 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1445 = false ∨ valuation q 1452 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1453 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1453)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 3 2 (meaning1439 q) (meaning1446 q) (meaning1453 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1446 = false ∨ valuation q 1453 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1454 = true := by
  have hs : count1449 q = (countLit q [-14, -16, -19, -20]) + (countLit q [-22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19, -20]) (l₂ := [-22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1454)) (countLit q [-14, -16, -19, -20]) (countLit q [-22, -25, -27, -29]) (count1449 q) 3 3 (meaning1439 q) (meaning1447 q) (meaning1454 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1447 = false ∨ valuation q 1454 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1427)) (literal (valuationOf q) (1458)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 2 (meaning1427 q) (meaning1458 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1458 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1459 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1459)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 2 1 (meaning1427 q) (meaning1449 q) (meaning1459 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1449 = false ∨ valuation q 1459 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1460 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1460)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 2 2 (meaning1427 q) (meaning1450 q) (meaning1460 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1450 = false ∨ valuation q 1460 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1461 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1461)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 2 3 (meaning1427 q) (meaning1451 q) (meaning1461 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1451 = false ∨ valuation q 1461 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1462 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1462)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 2 4 (meaning1427 q) (meaning1452 q) (meaning1462 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1452 = false ∨ valuation q 1462 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1463 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1463)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 2 5 (meaning1427 q) (meaning1453 q) (meaning1463 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1453 = false ∨ valuation q 1463 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1464 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 2 6 (meaning1427 q) (meaning1454 q) (meaning1464 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1454 = false ∨ valuation q 1464 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1459 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1428)) (literal (valuationOf q) (1459)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 3 (meaning1428 q) (meaning1459 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1459 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1460 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1460)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 3 1 (meaning1428 q) (meaning1449 q) (meaning1460 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1449 = false ∨ valuation q 1460 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1461 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1461)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 3 2 (meaning1428 q) (meaning1450 q) (meaning1461 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1450 = false ∨ valuation q 1461 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1462 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1462)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 3 3 (meaning1428 q) (meaning1451 q) (meaning1462 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1451 = false ∨ valuation q 1462 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1463 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1463)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 3 4 (meaning1428 q) (meaning1452 q) (meaning1463 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1452 = false ∨ valuation q 1463 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1464 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 3 5 (meaning1428 q) (meaning1453 q) (meaning1464 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1453 = false ∨ valuation q 1464 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1460 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1429)) (literal (valuationOf q) (1460)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 4 (meaning1429 q) (meaning1460 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1460 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1461 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1461)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 4 1 (meaning1429 q) (meaning1449 q) (meaning1461 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1449 = false ∨ valuation q 1461 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1462 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1462)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 4 2 (meaning1429 q) (meaning1450 q) (meaning1462 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1450 = false ∨ valuation q 1462 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1463 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1463)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 4 3 (meaning1429 q) (meaning1451 q) (meaning1463 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1451 = false ∨ valuation q 1463 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1464 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 4 4 (meaning1429 q) (meaning1452 q) (meaning1464 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1452 = false ∨ valuation q 1464 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E110.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112110
