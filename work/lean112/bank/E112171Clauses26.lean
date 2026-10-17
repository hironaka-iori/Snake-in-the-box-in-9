import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1483 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1483)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 3 8 (meaning1407 q) (meaning1466 q) (meaning1483 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1466 = false ∨ valuation q 1483 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1484 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1484)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 3 9 (meaning1407 q) (meaning1467 q) (meaning1484 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1467 = false ∨ valuation q 1484 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1478 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1460)) (literal (valuationOf q) (1478)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 4 2 (meaning1408 q) (meaning1460 q) (meaning1478 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1460 = false ∨ valuation q 1478 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1479 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1479)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 4 3 (meaning1408 q) (meaning1461 q) (meaning1479 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1461 = false ∨ valuation q 1479 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1480 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1480)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 4 4 (meaning1408 q) (meaning1462 q) (meaning1480 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1462 = false ∨ valuation q 1480 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1481 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1481)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 4 5 (meaning1408 q) (meaning1463 q) (meaning1481 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1463 = false ∨ valuation q 1481 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1482 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1482)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 4 6 (meaning1408 q) (meaning1464 q) (meaning1482 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1464 = false ∨ valuation q 1482 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1483 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1483)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 4 7 (meaning1408 q) (meaning1465 q) (meaning1483 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1465 = false ∨ valuation q 1483 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1484 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1408)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1484)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 4 8 (meaning1408 q) (meaning1466 q) (meaning1484 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1466 = false ∨ valuation q 1484 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1479 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1460)) (literal (valuationOf q) (1479)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 5 2 (meaning1409 q) (meaning1460 q) (meaning1479 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1460 = false ∨ valuation q 1479 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1480 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1480)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 5 3 (meaning1409 q) (meaning1461 q) (meaning1480 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1461 = false ∨ valuation q 1480 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1481 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1481)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 5 4 (meaning1409 q) (meaning1462 q) (meaning1481 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1462 = false ∨ valuation q 1481 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1482 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1482)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 5 5 (meaning1409 q) (meaning1463 q) (meaning1482 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1463 = false ∨ valuation q 1482 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1483 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1483)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 5 6 (meaning1409 q) (meaning1464 q) (meaning1483 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1464 = false ∨ valuation q 1483 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1484 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1484)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 5 7 (meaning1409 q) (meaning1465 q) (meaning1484 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1465 = false ∨ valuation q 1484 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1480 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1410)) (literal (valuationOf q) (1460)) (literal (valuationOf q) (1480)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 6 2 (meaning1410 q) (meaning1460 q) (meaning1480 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1460 = false ∨ valuation q 1480 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1481 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1410)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1481)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 6 3 (meaning1410 q) (meaning1461 q) (meaning1481 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1461 = false ∨ valuation q 1481 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1482 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1410)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1482)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 6 4 (meaning1410 q) (meaning1462 q) (meaning1482 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1462 = false ∨ valuation q 1482 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1483 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1410)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1483)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 6 5 (meaning1410 q) (meaning1463 q) (meaning1483 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1463 = false ∨ valuation q 1483 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-60]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1490)) (countLit q [-60]) (countLit q [-63]) (count1490 q) 1 (meaningNeg63 q) (meaning1490 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1490 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-60]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1490)) (countLit q [-60]) (countLit q [-63]) (count1490 q) 1 (meaningNeg60 q) (meaning1490 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1490 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1491 = true := by
  have hs : count1490 q = (countLit q [-60]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1491)) (countLit q [-60]) (countLit q [-63]) (count1490 q) 1 1 (meaningNeg60 q) (meaningNeg63 q) (meaning1491 q) hs
  change (! (valuationOf q 60)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 63 = true ∨ valuation q 1491 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-58]) + (countLit q [-60, -63]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60, -63])
  have hm := merge_right (literal (valuationOf q) (1490)) (literal (valuationOf q) (1492)) (countLit q [-58]) (countLit q [-60, -63]) (count1492 q) 1 (meaning1490 q) (meaning1492 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1492 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1493 = true := by
  have hs : count1492 q = (countLit q [-58]) + (countLit q [-60, -63]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60, -63])
  have hm := merge_right (literal (valuationOf q) (1491)) (literal (valuationOf q) (1493)) (countLit q [-58]) (countLit q [-60, -63]) (count1492 q) 2 (meaning1491 q) (meaning1493 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1493 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-58]) + (countLit q [-60, -63]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60, -63])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1492)) (countLit q [-58]) (countLit q [-60, -63]) (count1492 q) 1 (meaningNeg58 q) (meaning1492 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1492 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1490 = false ∨ valuationOf q 1493 = true := by
  have hs : count1492 q = (countLit q [-58]) + (countLit q [-60, -63]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60, -63])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1493)) (countLit q [-58]) (countLit q [-60, -63]) (count1492 q) 1 1 (meaningNeg58 q) (meaning1490 q) (meaning1493 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1490 = false ∨ valuation q 1493 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1491 = false ∨ valuationOf q 1494 = true := by
  have hs : count1492 q = (countLit q [-58]) + (countLit q [-60, -63]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60, -63])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1494)) (countLit q [-58]) (countLit q [-60, -63]) (count1492 q) 1 2 (meaningNeg58 q) (meaning1491 q) (meaning1494 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1491 = false ∨ valuation q 1494 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1495 = true := by
  have hs : count1495 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (1495)) (countLit q [-66]) (countLit q [-68]) (count1495 q) 1 (meaningNeg68 q) (meaning1495 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1495 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1495 = true := by
  have hs : count1495 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1495)) (countLit q [-66]) (countLit q [-68]) (count1495 q) 1 (meaningNeg66 q) (meaning1495 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1495 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 68 = true ∨ valuationOf q 1496 = true := by
  have hs : count1495 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-66)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (1496)) (countLit q [-66]) (countLit q [-68]) (count1495 q) 1 1 (meaningNeg66 q) (meaningNeg68 q) (meaning1496 q) hs
  change (! (valuationOf q 66)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 68 = true ∨ valuation q 1496 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1497)) (countLit q [-69]) (countLit q [-71]) (count1497 q) 1 (meaningNeg71 q) (meaning1497 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1497 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-69]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1497)) (countLit q [-69]) (countLit q [-71]) (count1497 q) 1 (meaningNeg69 q) (meaning1497 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1497 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E171.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112171
