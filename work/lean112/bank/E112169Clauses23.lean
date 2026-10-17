import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1421 = false ∨ valuationOf q 1424 = true := by
  have hs : count1423 q = (countLit q [-17]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1424)) (countLit q [-17]) (countLit q [-18, -19]) (count1423 q) 1 1 (meaningNeg17 q) (meaning1421 q) (meaning1424 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1421 = false ∨ valuation q 1424 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1422 = false ∨ valuationOf q 1425 = true := by
  have hs : count1423 q = (countLit q [-17]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1425)) (countLit q [-17]) (countLit q [-18, -19]) (count1423 q) 1 2 (meaningNeg17 q) (meaning1422 q) (meaning1425 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1422 = false ∨ valuation q 1425 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-21]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1426)) (countLit q [-21]) (countLit q [-24]) (count1426 q) 1 (meaningNeg24 q) (meaning1426 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1426 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-21]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1426)) (countLit q [-21]) (countLit q [-24]) (count1426 q) 1 (meaningNeg21 q) (meaning1426 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1426 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1427 = true := by
  have hs : count1426 q = (countLit q [-21]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1427)) (countLit q [-21]) (countLit q [-24]) (count1426 q) 1 1 (meaningNeg21 q) (meaningNeg24 q) (meaning1427 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 24 = true ∨ valuation q 1427 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_right (literal (valuationOf q) (-27)) (literal (valuationOf q) (1428)) (countLit q [-25]) (countLit q [-27]) (count1428 q) 1 (meaningNeg27 q) (meaning1428 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1428 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1428)) (countLit q [-25]) (countLit q [-27]) (count1428 q) 1 (meaningNeg25 q) (meaning1428 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1428 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 27 = true ∨ valuationOf q 1429 = true := by
  have hs : count1428 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-27)) (literal (valuationOf q) (1429)) (countLit q [-25]) (countLit q [-27]) (count1428 q) 1 1 (meaningNeg25 q) (meaningNeg27 q) (meaning1429 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 27)) = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 1429 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-21, -24]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -27])
  have hm := merge_right (literal (valuationOf q) (1428)) (literal (valuationOf q) (1430)) (countLit q [-21, -24]) (countLit q [-25, -27]) (count1430 q) 1 (meaning1428 q) (meaning1430 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1430 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-21, -24]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -27])
  have hm := merge_right (literal (valuationOf q) (1429)) (literal (valuationOf q) (1431)) (countLit q [-21, -24]) (countLit q [-25, -27]) (count1430 q) 2 (meaning1429 q) (meaning1431 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1431 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-21, -24]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -27])
  have hm := merge_left (literal (valuationOf q) (1426)) (literal (valuationOf q) (1430)) (countLit q [-21, -24]) (countLit q [-25, -27]) (count1430 q) 1 (meaning1426 q) (meaning1430 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1430 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-21, -24]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1431)) (countLit q [-21, -24]) (countLit q [-25, -27]) (count1430 q) 1 1 (meaning1426 q) (meaning1428 q) (meaning1431 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1428 = false ∨ valuation q 1431 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1432 = true := by
  have hs : count1430 q = (countLit q [-21, -24]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1432)) (countLit q [-21, -24]) (countLit q [-25, -27]) (count1430 q) 1 2 (meaning1426 q) (meaning1429 q) (meaning1432 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1429 = false ∨ valuation q 1432 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-21, -24]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -27])
  have hm := merge_left (literal (valuationOf q) (1427)) (literal (valuationOf q) (1431)) (countLit q [-21, -24]) (countLit q [-25, -27]) (count1430 q) 2 (meaning1427 q) (meaning1431 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1431 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1432 = true := by
  have hs : count1430 q = (countLit q [-21, -24]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1432)) (countLit q [-21, -24]) (countLit q [-25, -27]) (count1430 q) 2 1 (meaning1427 q) (meaning1428 q) (meaning1432 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1428 = false ∨ valuation q 1432 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 1430 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1430)) (literal (valuationOf q) (1434)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 1 (meaning1430 q) (meaning1434 q) hs
  change valuationOf q 1430 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 1430 = false ∨ valuation q 1434 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1431)) (literal (valuationOf q) (1435)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 2 (meaning1431 q) (meaning1435 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1435 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1432)) (literal (valuationOf q) (1436)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 3 (meaning1432 q) (meaning1436 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1436 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1423)) (literal (valuationOf q) (1434)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 1 (meaning1423 q) (meaning1434 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1434 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1435)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 1 1 (meaning1423 q) (meaning1430 q) (meaning1435 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1430 = false ∨ valuation q 1435 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1436)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 1 2 (meaning1423 q) (meaning1431 q) (meaning1436 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1431 = false ∨ valuation q 1436 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1437 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1437)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 1 3 (meaning1423 q) (meaning1432 q) (meaning1437 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1432 = false ∨ valuation q 1437 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1424)) (literal (valuationOf q) (1435)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 2 (meaning1424 q) (meaning1435 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1435 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1436)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 2 1 (meaning1424 q) (meaning1430 q) (meaning1436 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1430 = false ∨ valuation q 1436 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1437 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1437)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 2 2 (meaning1424 q) (meaning1431 q) (meaning1437 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1431 = false ∨ valuation q 1437 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_left (literal (valuationOf q) (1425)) (literal (valuationOf q) (1436)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 3 (meaning1425 q) (meaning1436 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1436 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1437 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1437)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 3 1 (meaning1425 q) (meaning1430 q) (meaning1437 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1430 = false ∨ valuation q 1437 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1438 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1438)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 3 2 (meaning1425 q) (meaning1431 q) (meaning1438 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1431 = false ∨ valuation q 1438 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1439 = true := by
  have hs : count1434 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -24, -25, -27])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1439)) (countLit q [-17, -18, -19]) (countLit q [-21, -24, -25, -27]) (count1434 q) 3 3 (meaning1425 q) (meaning1432 q) (meaning1439 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1432 = false ∨ valuation q 1439 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1434)) (literal (valuationOf q) (1441)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 1 (meaning1434 q) (meaning1441 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1441 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1435)) (literal (valuationOf q) (1442)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 2 (meaning1435 q) (meaning1442 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1442 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-2, -4, -5, -8, -9, -12, -13]) + (countLit q [-17, -18, -19, -21, -24, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13]) (l₂ := [-17, -18, -19, -21, -24, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1436)) (literal (valuationOf q) (1443)) (countLit q [-2, -4, -5, -8, -9, -12, -13]) (countLit q [-17, -18, -19, -21, -24, -25, -27]) (count1441 q) 3 (meaning1436 q) (meaning1443 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1443 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E169.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112169
