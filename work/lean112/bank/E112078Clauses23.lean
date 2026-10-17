import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1449 = true := by
  have hs : count1449 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1449)) (countLit q [-2]) (countLit q [-4, -5]) (count1449 q) 1 (meaningNeg2 q) (meaning1449 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1449 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1450)) (countLit q [-2]) (countLit q [-4, -5]) (count1449 q) 1 1 (meaningNeg2 q) (meaning1447 q) (meaning1450 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1447 = false ∨ valuation q 1450 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1448 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1451)) (countLit q [-2]) (countLit q [-4, -5]) (count1449 q) 1 2 (meaningNeg2 q) (meaning1448 q) (meaning1451 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1448 = false ∨ valuation q 1451 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1452)) (countLit q [-6]) (countLit q [-7]) (count1452 q) 1 (meaningNeg7 q) (meaning1452 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1452 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1452)) (countLit q [-6]) (countLit q [-7]) (count1452 q) 1 (meaningNeg6 q) (meaning1452 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1452 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1453)) (countLit q [-6]) (countLit q [-7]) (count1452 q) 1 1 (meaningNeg6 q) (meaningNeg7 q) (meaning1453 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 1453 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1454)) (countLit q [-8]) (countLit q [-11]) (count1454 q) 1 (meaningNeg11 q) (meaning1454 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1454 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1454)) (countLit q [-8]) (countLit q [-11]) (count1454 q) 1 (meaningNeg8 q) (meaning1454 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1454 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 11 = true ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-8]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (1455)) (countLit q [-8]) (countLit q [-11]) (count1454 q) 1 1 (meaningNeg8 q) (meaningNeg11 q) (meaning1455 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 11 = true ∨ valuation q 1455 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-6, -7]) + (countLit q [-8, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -11])
  have hm := merge_right (literal (valuationOf q) (1454)) (literal (valuationOf q) (1456)) (countLit q [-6, -7]) (countLit q [-8, -11]) (count1456 q) 1 (meaning1454 q) (meaning1456 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1456 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-6, -7]) + (countLit q [-8, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -11])
  have hm := merge_right (literal (valuationOf q) (1455)) (literal (valuationOf q) (1457)) (countLit q [-6, -7]) (countLit q [-8, -11]) (count1456 q) 2 (meaning1455 q) (meaning1457 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1457 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-6, -7]) + (countLit q [-8, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -11])
  have hm := merge_left (literal (valuationOf q) (1452)) (literal (valuationOf q) (1456)) (countLit q [-6, -7]) (countLit q [-8, -11]) (count1456 q) 1 (meaning1452 q) (meaning1456 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1456 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-6, -7]) + (countLit q [-8, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -11])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1457)) (countLit q [-6, -7]) (countLit q [-8, -11]) (count1456 q) 1 1 (meaning1452 q) (meaning1454 q) (meaning1457 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1454 = false ∨ valuation q 1457 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1458 = true := by
  have hs : count1456 q = (countLit q [-6, -7]) + (countLit q [-8, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -11])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1458)) (countLit q [-6, -7]) (countLit q [-8, -11]) (count1456 q) 1 2 (meaning1452 q) (meaning1455 q) (meaning1458 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1455 = false ∨ valuation q 1458 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-6, -7]) + (countLit q [-8, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -11])
  have hm := merge_left (literal (valuationOf q) (1453)) (literal (valuationOf q) (1457)) (countLit q [-6, -7]) (countLit q [-8, -11]) (count1456 q) 2 (meaning1453 q) (meaning1457 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1457 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1458 = true := by
  have hs : count1456 q = (countLit q [-6, -7]) + (countLit q [-8, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -11])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1458)) (countLit q [-6, -7]) (countLit q [-8, -11]) (count1456 q) 2 1 (meaning1453 q) (meaning1454 q) (meaning1458 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1454 = false ∨ valuation q 1458 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1459 = true := by
  have hs : count1456 q = (countLit q [-6, -7]) + (countLit q [-8, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -11])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1459)) (countLit q [-6, -7]) (countLit q [-8, -11]) (count1456 q) 2 2 (meaning1453 q) (meaning1455 q) (meaning1459 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1455 = false ∨ valuation q 1459 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1460 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_right (literal (valuationOf q) (1456)) (literal (valuationOf q) (1460)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 1 (meaning1456 q) (meaning1460 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1460 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1461 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_right (literal (valuationOf q) (1457)) (literal (valuationOf q) (1461)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 2 (meaning1457 q) (meaning1461 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1461 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1462 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_right (literal (valuationOf q) (1458)) (literal (valuationOf q) (1462)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 3 (meaning1458 q) (meaning1462 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1462 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1463 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_right (literal (valuationOf q) (1459)) (literal (valuationOf q) (1463)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 4 (meaning1459 q) (meaning1463 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1463 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1460 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_left (literal (valuationOf q) (1449)) (literal (valuationOf q) (1460)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 1 (meaning1449 q) (meaning1460 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1460 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1461 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1461)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 1 1 (meaning1449 q) (meaning1456 q) (meaning1461 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1456 = false ∨ valuation q 1461 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1462 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1462)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 1 2 (meaning1449 q) (meaning1457 q) (meaning1462 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1457 = false ∨ valuation q 1462 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1463 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1463)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 1 3 (meaning1449 q) (meaning1458 q) (meaning1463 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1458 = false ∨ valuation q 1463 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1464 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1459)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 1 4 (meaning1449 q) (meaning1459 q) (meaning1464 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1459 = false ∨ valuation q 1464 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1461 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_left (literal (valuationOf q) (1450)) (literal (valuationOf q) (1461)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 2 (meaning1450 q) (meaning1461 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1461 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1462 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1462)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 2 1 (meaning1450 q) (meaning1456 q) (meaning1462 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1456 = false ∨ valuation q 1462 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1463 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1463)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 2 2 (meaning1450 q) (meaning1457 q) (meaning1463 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1457 = false ∨ valuation q 1463 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1464 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1450)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1464)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 2 3 (meaning1450 q) (meaning1458 q) (meaning1464 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1458 = false ∨ valuation q 1464 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1462 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_left (literal (valuationOf q) (1451)) (literal (valuationOf q) (1462)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 3 (meaning1451 q) (meaning1462 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1462 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1463 = true := by
  have hs : count1460 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -7, -8, -11]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -7, -8, -11])
  have hm := merge_two (literal (valuationOf q) (1451)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1463)) (countLit q [-2, -4, -5]) (countLit q [-6, -7, -8, -11]) (count1460 q) 3 1 (meaning1451 q) (meaning1456 q) (meaning1463 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1456 = false ∨ valuation q 1463 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E078.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112078
