import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1473 = true := by
  have hs : count1473 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1473)) (countLit q [-25]) (countLit q [-26]) (count1473 q) 1 (meaningNeg25 q) (meaning1473 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1473 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 26 = true ∨ valuationOf q 1474 = true := by
  have hs : count1473 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (1474)) (countLit q [-25]) (countLit q [-26]) (count1473 q) 1 1 (meaningNeg25 q) (meaningNeg26 q) (meaning1474 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 26 = true ∨ valuation q 1474 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_right (literal (valuationOf q) (1473)) (literal (valuationOf q) (1475)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 1 (meaning1473 q) (meaning1475 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1475 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1476 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_right (literal (valuationOf q) (1474)) (literal (valuationOf q) (1476)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 2 (meaning1474 q) (meaning1476 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1476 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_left (literal (valuationOf q) (1471)) (literal (valuationOf q) (1475)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 1 (meaning1471 q) (meaning1475 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1475 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1476 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1476)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 1 1 (meaning1471 q) (meaning1473 q) (meaning1476 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1473 = false ∨ valuation q 1476 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1477 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1477)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 1 2 (meaning1471 q) (meaning1474 q) (meaning1477 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1474 = false ∨ valuation q 1477 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1476 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_left (literal (valuationOf q) (1472)) (literal (valuationOf q) (1476)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 2 (meaning1472 q) (meaning1476 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1476 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1477 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1477)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 2 1 (meaning1472 q) (meaning1473 q) (meaning1477 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1473 = false ∨ valuation q 1477 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1478 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 2 2 (meaning1472 q) (meaning1474 q) (meaning1478 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = false ∨ valuation q 1478 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1479)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 1 (meaning1475 q) (meaning1479 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1479 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1480 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1480)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 2 (meaning1476 q) (meaning1480 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1480 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1481 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1477)) (literal (valuationOf q) (1481)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 3 (meaning1477 q) (meaning1481 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1481 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1482 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1478)) (literal (valuationOf q) (1482)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 4 (meaning1478 q) (meaning1482 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1482 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1467)) (literal (valuationOf q) (1479)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 1 (meaning1467 q) (meaning1479 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1479 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1480 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1480)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 1 1 (meaning1467 q) (meaning1475 q) (meaning1480 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1475 = false ∨ valuation q 1480 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1481 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1481)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 1 2 (meaning1467 q) (meaning1476 q) (meaning1481 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1476 = false ∨ valuation q 1481 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1482 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1482)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 1 3 (meaning1467 q) (meaning1477 q) (meaning1482 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1477 = false ∨ valuation q 1482 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1483 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1483)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 1 4 (meaning1467 q) (meaning1478 q) (meaning1483 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1478 = false ∨ valuation q 1483 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1480 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1468)) (literal (valuationOf q) (1480)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 2 (meaning1468 q) (meaning1480 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1480 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1481)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 2 1 (meaning1468 q) (meaning1475 q) (meaning1481 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1475 = false ∨ valuation q 1481 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1482 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1482)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 2 2 (meaning1468 q) (meaning1476 q) (meaning1482 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1476 = false ∨ valuation q 1482 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1483 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1483)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 2 3 (meaning1468 q) (meaning1477 q) (meaning1483 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1477 = false ∨ valuation q 1483 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1484 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1484)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 2 4 (meaning1468 q) (meaning1478 q) (meaning1484 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1478 = false ∨ valuation q 1484 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1481 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1469)) (literal (valuationOf q) (1481)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 3 (meaning1469 q) (meaning1481 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1481 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1482 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1482)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 3 1 (meaning1469 q) (meaning1475 q) (meaning1482 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1475 = false ∨ valuation q 1482 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1483 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1483)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 3 2 (meaning1469 q) (meaning1476 q) (meaning1483 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1476 = false ∨ valuation q 1483 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1484 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1484)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 3 3 (meaning1469 q) (meaning1477 q) (meaning1484 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1477 = false ∨ valuation q 1484 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1482 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1470)) (literal (valuationOf q) (1482)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 4 (meaning1470 q) (meaning1482 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1482 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1483 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1483)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 4 1 (meaning1470 q) (meaning1475 q) (meaning1483 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1475 = false ∨ valuation q 1483 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1492)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 1 5 (meaning1456 q) (meaning1483 q) (meaning1492 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1483 = false ∨ valuation q 1492 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true := by
  have hs : count1487 q = (countLit q [-1, -3, -5, -6, -8, -10, -11]) + (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11]) (l₂ := [-13, -14, -18, -19, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1489)) (countLit q [-1, -3, -5, -6, -8, -10, -11]) (countLit q [-13, -14, -18, -19, -20, -22, -25, -26]) (count1487 q) 2 1 (meaning1457 q) (meaning1479 q) (meaning1489 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1479 = false ∨ valuation q 1489 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E024.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112024
