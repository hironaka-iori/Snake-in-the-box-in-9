import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_right (literal (valuationOf q) (-14)) (literal (valuationOf q) (1463)) (countLit q [-13]) (countLit q [-14]) (count1463 q) 1 (meaningNeg14 q) (meaning1463 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1463 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1463)) (countLit q [-13]) (countLit q [-14]) (count1463 q) 1 (meaningNeg13 q) (meaning1463 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1463 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 14 = true ∨ valuationOf q 1464 = true := by
  have hs : count1463 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-14)) (literal (valuationOf q) (1464)) (countLit q [-13]) (countLit q [-14]) (count1463 q) 1 1 (meaningNeg13 q) (meaningNeg14 q) (meaning1464 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 14)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 1464 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1465)) (countLit q [-18]) (countLit q [-19]) (count1465 q) 1 (meaningNeg19 q) (meaning1465 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1465 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1465)) (countLit q [-18]) (countLit q [-19]) (count1465 q) 1 (meaningNeg18 q) (meaning1465 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1465 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 19 = true ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (1466)) (countLit q [-18]) (countLit q [-19]) (count1465 q) 1 1 (meaningNeg18 q) (meaningNeg19 q) (meaning1466 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 1466 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1467)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 1 (meaning1465 q) (meaning1467 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1467 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_right (literal (valuationOf q) (1466)) (literal (valuationOf q) (1468)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 2 (meaning1466 q) (meaning1468 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1468 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_left (literal (valuationOf q) (1463)) (literal (valuationOf q) (1467)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 1 (meaning1463 q) (meaning1467 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1467 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1468)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 1 1 (meaning1463 q) (meaning1465 q) (meaning1468 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1465 = false ∨ valuation q 1468 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1469 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1469)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 1 2 (meaning1463 q) (meaning1466 q) (meaning1469 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1466 = false ∨ valuation q 1469 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_left (literal (valuationOf q) (1464)) (literal (valuationOf q) (1468)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 2 (meaning1464 q) (meaning1468 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1468 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1469 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1469)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 2 1 (meaning1464 q) (meaning1465 q) (meaning1469 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1465 = false ∨ valuation q 1469 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1470 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1470)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 2 2 (meaning1464 q) (meaning1466 q) (meaning1470 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1466 = false ∨ valuation q 1470 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1471)) (countLit q [-20]) (countLit q [-22]) (count1471 q) 1 (meaningNeg22 q) (meaning1471 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1471 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1471)) (countLit q [-20]) (countLit q [-22]) (count1471 q) 1 (meaningNeg20 q) (meaning1471 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1471 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1472 = true := by
  have hs : count1471 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1472)) (countLit q [-20]) (countLit q [-22]) (count1471 q) 1 1 (meaningNeg20 q) (meaningNeg22 q) (meaning1472 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 1472 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1473 = true := by
  have hs : count1473 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1473)) (countLit q [-25]) (countLit q [-26]) (count1473 q) 1 (meaningNeg26 q) (meaning1473 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1473 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1473 = true := by
  have hs : count1473 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1473)) (countLit q [-25]) (countLit q [-26]) (count1473 q) 1 (meaningNeg25 q) (meaning1473 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1473 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 26 = true ∨ valuationOf q 1474 = true := by
  have hs : count1473 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (1474)) (countLit q [-25]) (countLit q [-26]) (count1473 q) 1 1 (meaningNeg25 q) (meaningNeg26 q) (meaning1474 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 26 = true ∨ valuation q 1474 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_right (literal (valuationOf q) (1473)) (literal (valuationOf q) (1475)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 1 (meaning1473 q) (meaning1475 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1475 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1476 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_right (literal (valuationOf q) (1474)) (literal (valuationOf q) (1476)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 2 (meaning1474 q) (meaning1476 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1476 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_left (literal (valuationOf q) (1471)) (literal (valuationOf q) (1475)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 1 (meaning1471 q) (meaning1475 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1475 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1476 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1476)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 1 1 (meaning1471 q) (meaning1473 q) (meaning1476 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1473 = false ∨ valuation q 1476 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1477 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1477)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 1 2 (meaning1471 q) (meaning1474 q) (meaning1477 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1474 = false ∨ valuation q 1477 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1476 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_left (literal (valuationOf q) (1472)) (literal (valuationOf q) (1476)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 2 (meaning1472 q) (meaning1476 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1476 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1477 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1477)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 2 1 (meaning1472 q) (meaning1473 q) (meaning1477 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1473 = false ∨ valuation q 1477 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1478 = true := by
  have hs : count1475 q = (countLit q [-20, -22]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (countLit q [-20, -22]) (countLit q [-25, -26]) (count1475 q) 2 2 (meaning1472 q) (meaning1474 q) (meaning1478 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = false ∨ valuation q 1478 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1479)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 1 (meaning1475 q) (meaning1479 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1479 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1480 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1480)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 2 (meaning1476 q) (meaning1480 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1480 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1481 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1477)) (literal (valuationOf q) (1481)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 3 (meaning1477 q) (meaning1481 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1481 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-13, -14, -18, -19]) + (countLit q [-20, -22, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -18, -19]) (l₂ := [-20, -22, -25, -26])
  have hm := merge_left (literal (valuationOf q) (1467)) (literal (valuationOf q) (1479)) (countLit q [-13, -14, -18, -19]) (countLit q [-20, -22, -25, -26]) (count1479 q) 1 (meaning1467 q) (meaning1479 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1479 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E026.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112026
