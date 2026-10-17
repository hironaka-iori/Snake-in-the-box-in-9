import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1461 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1430)) (literal (valuationOf q) (1461)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 5 (meaning1430 q) (meaning1461 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1461 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1462 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1462)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 5 1 (meaning1430 q) (meaning1449 q) (meaning1462 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1449 = false ∨ valuation q 1462 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1463 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1463)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 5 2 (meaning1430 q) (meaning1450 q) (meaning1463 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1450 = false ∨ valuation q 1463 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1464 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1430)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 5 3 (meaning1430 q) (meaning1451 q) (meaning1464 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1451 = false ∨ valuation q 1464 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1462 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1431)) (literal (valuationOf q) (1462)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 6 (meaning1431 q) (meaning1462 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1462 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1463 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1463)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 6 1 (meaning1431 q) (meaning1449 q) (meaning1463 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1449 = false ∨ valuation q 1463 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1464 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 6 2 (meaning1431 q) (meaning1450 q) (meaning1464 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1450 = false ∨ valuation q 1464 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1465 = true := by
  have hs : count1457 q = (countLit q [-2, -4, -5, -6, -9, -11, -13]) + (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13]) (l₂ := [-14, -16, -19, -20, -22, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1465)) (countLit q [-2, -4, -5, -6, -9, -11, -13]) (countLit q [-14, -16, -19, -20, -22, -25, -27, -29]) (count1457 q) 6 3 (meaning1431 q) (meaning1451 q) (meaning1465 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1451 = false ∨ valuation q 1465 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-32]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1472)) (countLit q [-32]) (countLit q [-35]) (count1472 q) 1 (meaningNeg35 q) (meaning1472 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1472 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-32]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1472)) (countLit q [-32]) (countLit q [-35]) (count1472 q) 1 (meaningNeg32 q) (meaning1472 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1472 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-32]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1473)) (countLit q [-32]) (countLit q [-35]) (count1472 q) 1 1 (meaningNeg32 q) (meaningNeg35 q) (meaning1473 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 35 = true ∨ valuation q 1473 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-30]) + (countLit q [-32, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -35])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (countLit q [-30]) (countLit q [-32, -35]) (count1474 q) 1 (meaning1472 q) (meaning1474 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-30]) + (countLit q [-32, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -35])
  have hm := merge_right (literal (valuationOf q) (1473)) (literal (valuationOf q) (1475)) (countLit q [-30]) (countLit q [-32, -35]) (count1474 q) 2 (meaning1473 q) (meaning1475 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1475 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-30]) + (countLit q [-32, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -35])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1474)) (countLit q [-30]) (countLit q [-32, -35]) (count1474 q) 1 (meaningNeg30 q) (meaning1474 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1474 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-30]) + (countLit q [-32, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -35])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1475)) (countLit q [-30]) (countLit q [-32, -35]) (count1474 q) 1 1 (meaningNeg30 q) (meaning1472 q) (meaning1475 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1472 = false ∨ valuation q 1475 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1473 = false ∨ valuationOf q 1476 = true := by
  have hs : count1474 q = (countLit q [-30]) + (countLit q [-32, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -35])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1476)) (countLit q [-30]) (countLit q [-32, -35]) (count1474 q) 1 2 (meaningNeg30 q) (meaning1473 q) (meaning1476 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1473 = false ∨ valuation q 1476 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (1477)) (countLit q [-37]) (countLit q [-38]) (count1477 q) 1 (meaningNeg38 q) (meaning1477 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1477 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1477)) (countLit q [-37]) (countLit q [-38]) (count1477 q) 1 (meaningNeg37 q) (meaning1477 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1477 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 38 = true ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (1478)) (countLit q [-37]) (countLit q [-38]) (count1477 q) 1 1 (meaningNeg37 q) (meaningNeg38 q) (meaning1478 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 1478 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1479)) (countLit q [-40]) (countLit q [-42]) (count1479 q) 1 (meaningNeg42 q) (meaning1479 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1479 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1479)) (countLit q [-40]) (countLit q [-42]) (count1479 q) 1 (meaningNeg40 q) (meaning1479 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1479 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1480 = true := by
  have hs : count1479 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1480)) (countLit q [-40]) (countLit q [-42]) (count1479 q) 1 1 (meaningNeg40 q) (meaningNeg42 q) (meaning1480 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 1480 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-37, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1481)) (countLit q [-37, -38]) (countLit q [-40, -42]) (count1481 q) 1 (meaning1479 q) (meaning1481 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1481 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-37, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1480)) (literal (valuationOf q) (1482)) (countLit q [-37, -38]) (countLit q [-40, -42]) (count1481 q) 2 (meaning1480 q) (meaning1482 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1482 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-37, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -42])
  have hm := merge_left (literal (valuationOf q) (1477)) (literal (valuationOf q) (1481)) (countLit q [-37, -38]) (countLit q [-40, -42]) (count1481 q) 1 (meaning1477 q) (meaning1481 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1481 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-37, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1482)) (countLit q [-37, -38]) (countLit q [-40, -42]) (count1481 q) 1 1 (meaning1477 q) (meaning1479 q) (meaning1482 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1479 = false ∨ valuation q 1482 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-37, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1483)) (countLit q [-37, -38]) (countLit q [-40, -42]) (count1481 q) 1 2 (meaning1477 q) (meaning1480 q) (meaning1483 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1480 = false ∨ valuation q 1483 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-37, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -42])
  have hm := merge_left (literal (valuationOf q) (1478)) (literal (valuationOf q) (1482)) (countLit q [-37, -38]) (countLit q [-40, -42]) (count1481 q) 2 (meaning1478 q) (meaning1482 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1482 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-37, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1483)) (countLit q [-37, -38]) (countLit q [-40, -42]) (count1481 q) 2 1 (meaning1478 q) (meaning1479 q) (meaning1483 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1479 = false ∨ valuation q 1483 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1484 = true := by
  have hs : count1481 q = (countLit q [-37, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-37, -38]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1484)) (countLit q [-37, -38]) (countLit q [-40, -42]) (count1481 q) 2 2 (meaning1478 q) (meaning1480 q) (meaning1484 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1480 = false ∨ valuation q 1484 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1481)) (literal (valuationOf q) (1485)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 1 (meaning1481 q) (meaning1485 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1485 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-30, -32, -35]) + (countLit q [-37, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35]) (l₂ := [-37, -38, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1486)) (countLit q [-30, -32, -35]) (countLit q [-37, -38, -40, -42]) (count1485 q) 2 (meaning1482 q) (meaning1486 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1486 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E110.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112110
