import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1495 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1495)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 4 5 (meaning1463 q) (meaning1484 q) (meaning1495 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1484 = false ∨ valuation q 1495 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1491 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1464)) (literal (valuationOf q) (1491)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 5 (meaning1464 q) (meaning1491 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1491 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1492)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 5 1 (meaning1464 q) (meaning1480 q) (meaning1492 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1480 = false ∨ valuation q 1492 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1493 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1493)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 5 2 (meaning1464 q) (meaning1481 q) (meaning1493 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1481 = false ∨ valuation q 1493 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1494 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1494)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 5 3 (meaning1464 q) (meaning1482 q) (meaning1494 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1482 = false ∨ valuation q 1494 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1495 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -5, -6, -7, -8, -11]) + (countLit q [-13, -14, -17, -20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11]) (l₂ := [-13, -14, -17, -20, -22, -25, -26])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1495)) (countLit q [-2, -4, -5, -6, -7, -8, -11]) (countLit q [-13, -14, -17, -20, -22, -25, -26]) (count1487 q) 5 4 (meaning1464 q) (meaning1483 q) (meaning1495 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1483 = false ∨ valuation q 1495 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-30]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32])
  have hm := merge_right (literal (valuationOf q) (-32)) (literal (valuationOf q) (1501)) (countLit q [-30]) (countLit q [-32]) (count1501 q) 1 (meaningNeg32 q) (meaning1501 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1501 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-30]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1501)) (countLit q [-30]) (countLit q [-32]) (count1501 q) 1 (meaningNeg30 q) (meaning1501 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1501 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 32 = true ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-30]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (-32)) (literal (valuationOf q) (1502)) (countLit q [-30]) (countLit q [-32]) (count1501 q) 1 1 (meaningNeg30 q) (meaningNeg32 q) (meaning1502 q) hs
  change (! (valuationOf q 30)) = false ∨ (! (valuationOf q 32)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 32 = true ∨ valuation q 1502 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-27]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -32])
  have hm := merge_right (literal (valuationOf q) (1501)) (literal (valuationOf q) (1503)) (countLit q [-27]) (countLit q [-30, -32]) (count1503 q) 1 (meaning1501 q) (meaning1503 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1503 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-27]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -32])
  have hm := merge_right (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (countLit q [-27]) (countLit q [-30, -32]) (count1503 q) 2 (meaning1502 q) (meaning1504 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-27]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -32])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1503)) (countLit q [-27]) (countLit q [-30, -32]) (count1503 q) 1 (meaningNeg27 q) (meaning1503 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1503 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1501 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-27]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -32])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1504)) (countLit q [-27]) (countLit q [-30, -32]) (count1503 q) 1 1 (meaningNeg27 q) (meaning1501 q) (meaning1504 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1501 = false ∨ valuation q 1504 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true := by
  have hs : count1503 q = (countLit q [-27]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -32])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (countLit q [-27]) (countLit q [-30, -32]) (count1503 q) 1 2 (meaningNeg27 q) (meaning1502 q) (meaning1505 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1502 = false ∨ valuation q 1505 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-35]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (1506)) (countLit q [-35]) (countLit q [-38]) (count1506 q) 1 (meaningNeg38 q) (meaning1506 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1506 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-35]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1506)) (countLit q [-35]) (countLit q [-38]) (count1506 q) 1 (meaningNeg35 q) (meaning1506 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1506 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 38 = true ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-35]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (1507)) (countLit q [-35]) (countLit q [-38]) (count1506 q) 1 1 (meaningNeg35 q) (meaningNeg38 q) (meaning1507 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 38 = true ∨ valuation q 1507 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1508)) (countLit q [-39]) (countLit q [-42]) (count1508 q) 1 (meaningNeg42 q) (meaning1508 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1508 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1508)) (countLit q [-39]) (countLit q [-42]) (count1508 q) 1 (meaningNeg39 q) (meaning1508 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1508 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1509)) (countLit q [-39]) (countLit q [-42]) (count1508 q) 1 1 (meaningNeg39 q) (meaningNeg42 q) (meaning1509 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 42 = true ∨ valuation q 1509 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-35, -38]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -38]) (l₂ := [-39, -42])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1510)) (countLit q [-35, -38]) (countLit q [-39, -42]) (count1510 q) 1 (meaning1508 q) (meaning1510 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1510 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-35, -38]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -38]) (l₂ := [-39, -42])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1511)) (countLit q [-35, -38]) (countLit q [-39, -42]) (count1510 q) 2 (meaning1509 q) (meaning1511 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1511 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-35, -38]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -38]) (l₂ := [-39, -42])
  have hm := merge_left (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-35, -38]) (countLit q [-39, -42]) (count1510 q) 1 (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1510 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-35, -38]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -38]) (l₂ := [-39, -42])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1511)) (countLit q [-35, -38]) (countLit q [-39, -42]) (count1510 q) 1 1 (meaning1506 q) (meaning1508 q) (meaning1511 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = false ∨ valuation q 1511 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-35, -38]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -38]) (l₂ := [-39, -42])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1512)) (countLit q [-35, -38]) (countLit q [-39, -42]) (count1510 q) 1 2 (meaning1506 q) (meaning1509 q) (meaning1512 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1509 = false ∨ valuation q 1512 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-35, -38]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -38]) (l₂ := [-39, -42])
  have hm := merge_left (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-35, -38]) (countLit q [-39, -42]) (count1510 q) 2 (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1511 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1512 = true := by
  have hs : count1510 q = (countLit q [-35, -38]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -38]) (l₂ := [-39, -42])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1512)) (countLit q [-35, -38]) (countLit q [-39, -42]) (count1510 q) 2 1 (meaning1507 q) (meaning1508 q) (meaning1512 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1508 = false ∨ valuation q 1512 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1513 = true := by
  have hs : count1510 q = (countLit q [-35, -38]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -38]) (l₂ := [-39, -42])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1513)) (countLit q [-35, -38]) (countLit q [-39, -42]) (count1510 q) 2 2 (meaning1507 q) (meaning1509 q) (meaning1513 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1509 = false ∨ valuation q 1513 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_right (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 1 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_right (literal (valuationOf q) (1511)) (literal (valuationOf q) (1515)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 2 (meaning1511 q) (meaning1515 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1515 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1516)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 3 (meaning1512 q) (meaning1516 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1516 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1517 = true := by
  have hs : count1514 q = (countLit q [-27, -30, -32]) + (countLit q [-35, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32]) (l₂ := [-35, -38, -39, -42])
  have hm := merge_right (literal (valuationOf q) (1513)) (literal (valuationOf q) (1517)) (countLit q [-27, -30, -32]) (countLit q [-35, -38, -39, -42]) (count1514 q) 4 (meaning1513 q) (meaning1517 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1517 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E078.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112078
