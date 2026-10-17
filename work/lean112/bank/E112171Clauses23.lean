import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_right (literal (valuationOf q) (1420)) (literal (valuationOf q) (1422)) (countLit q [-30]) (countLit q [-32, -34]) (count1421 q) 2 (meaning1420 q) (meaning1422 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1422 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1421)) (countLit q [-30]) (countLit q [-32, -34]) (count1421 q) 1 (meaningNeg30 q) (meaning1421 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1421 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1419 = false ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1422)) (countLit q [-30]) (countLit q [-32, -34]) (count1421 q) 1 1 (meaningNeg30 q) (meaning1419 q) (meaning1422 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1419 = false ∨ valuation q 1422 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1420 = false ∨ valuationOf q 1423 = true := by
  have hs : count1421 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1423)) (countLit q [-30]) (countLit q [-32, -34]) (count1421 q) 1 2 (meaningNeg30 q) (meaning1420 q) (meaning1423 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1420 = false ∨ valuation q 1423 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1424 = true := by
  have hs : count1424 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1424)) (countLit q [-35]) (countLit q [-36]) (count1424 q) 1 (meaningNeg36 q) (meaning1424 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1424 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1424 = true := by
  have hs : count1424 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1424)) (countLit q [-35]) (countLit q [-36]) (count1424 q) 1 (meaningNeg35 q) (meaning1424 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1424 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1426)) (countLit q [-40]) (countLit q [-42]) (count1426 q) 1 (meaningNeg42 q) (meaning1426 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1426 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1426)) (countLit q [-40]) (countLit q [-42]) (count1426 q) 1 (meaningNeg40 q) (meaning1426 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1426 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1427 = true := by
  have hs : count1426 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1427)) (countLit q [-40]) (countLit q [-42]) (count1426 q) 1 1 (meaningNeg40 q) (meaningNeg42 q) (meaning1427 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 1427 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-35, -36]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1426)) (literal (valuationOf q) (1428)) (countLit q [-35, -36]) (countLit q [-40, -42]) (count1428 q) 1 (meaning1426 q) (meaning1428 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1428 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1429 = true := by
  have hs : count1428 q = (countLit q [-35, -36]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1427)) (literal (valuationOf q) (1429)) (countLit q [-35, -36]) (countLit q [-40, -42]) (count1428 q) 2 (meaning1427 q) (meaning1429 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1429 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-35, -36]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-40, -42])
  have hm := merge_left (literal (valuationOf q) (1424)) (literal (valuationOf q) (1428)) (countLit q [-35, -36]) (countLit q [-40, -42]) (count1428 q) 1 (meaning1424 q) (meaning1428 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1428 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1429 = true := by
  have hs : count1428 q = (countLit q [-35, -36]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1426)) (literal (valuationOf q) (1429)) (countLit q [-35, -36]) (countLit q [-40, -42]) (count1428 q) 1 1 (meaning1424 q) (meaning1426 q) (meaning1429 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1426 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1426 = false ∨ valuation q 1429 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1432 = true := by
  have hs : count1432 q = (countLit q [-30, -32, -34]) + (countLit q [-35, -36, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-35, -36, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1428)) (literal (valuationOf q) (1432)) (countLit q [-30, -32, -34]) (countLit q [-35, -36, -40, -42]) (count1432 q) 1 (meaning1428 q) (meaning1432 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1432 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1433 = true := by
  have hs : count1432 q = (countLit q [-30, -32, -34]) + (countLit q [-35, -36, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-35, -36, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1429)) (literal (valuationOf q) (1433)) (countLit q [-30, -32, -34]) (countLit q [-35, -36, -40, -42]) (count1432 q) 2 (meaning1429 q) (meaning1433 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1433 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1432 = true := by
  have hs : count1432 q = (countLit q [-30, -32, -34]) + (countLit q [-35, -36, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-35, -36, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1421)) (literal (valuationOf q) (1432)) (countLit q [-30, -32, -34]) (countLit q [-35, -36, -40, -42]) (count1432 q) 1 (meaning1421 q) (meaning1432 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1432 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1433 = true := by
  have hs : count1432 q = (countLit q [-30, -32, -34]) + (countLit q [-35, -36, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-35, -36, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1421)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1433)) (countLit q [-30, -32, -34]) (countLit q [-35, -36, -40, -42]) (count1432 q) 1 1 (meaning1421 q) (meaning1428 q) (meaning1433 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1428 = false ∨ valuation q 1433 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1434 = true := by
  have hs : count1432 q = (countLit q [-30, -32, -34]) + (countLit q [-35, -36, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-35, -36, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1421)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1434)) (countLit q [-30, -32, -34]) (countLit q [-35, -36, -40, -42]) (count1432 q) 1 2 (meaning1421 q) (meaning1429 q) (meaning1434 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1429 = false ∨ valuation q 1434 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1433 = true := by
  have hs : count1432 q = (countLit q [-30, -32, -34]) + (countLit q [-35, -36, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-35, -36, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1422)) (literal (valuationOf q) (1433)) (countLit q [-30, -32, -34]) (countLit q [-35, -36, -40, -42]) (count1432 q) 2 (meaning1422 q) (meaning1433 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1433 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1434 = true := by
  have hs : count1432 q = (countLit q [-30, -32, -34]) + (countLit q [-35, -36, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-35, -36, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1422)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1434)) (countLit q [-30, -32, -34]) (countLit q [-35, -36, -40, -42]) (count1432 q) 2 1 (meaning1422 q) (meaning1428 q) (meaning1434 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1428 = false ∨ valuation q 1434 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1435 = true := by
  have hs : count1432 q = (countLit q [-30, -32, -34]) + (countLit q [-35, -36, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-35, -36, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1422)) (literal (valuationOf q) (1429)) (literal (valuationOf q) (1435)) (countLit q [-30, -32, -34]) (countLit q [-35, -36, -40, -42]) (count1432 q) 2 2 (meaning1422 q) (meaning1429 q) (meaning1435 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1429 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1429 = false ∨ valuation q 1435 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1434 = true := by
  have hs : count1432 q = (countLit q [-30, -32, -34]) + (countLit q [-35, -36, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-35, -36, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1423)) (literal (valuationOf q) (1434)) (countLit q [-30, -32, -34]) (countLit q [-35, -36, -40, -42]) (count1432 q) 3 (meaning1423 q) (meaning1434 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1434 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1435 = true := by
  have hs : count1432 q = (countLit q [-30, -32, -34]) + (countLit q [-35, -36, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-35, -36, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1435)) (countLit q [-30, -32, -34]) (countLit q [-35, -36, -40, -42]) (count1432 q) 3 1 (meaning1423 q) (meaning1428 q) (meaning1435 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1428 = false ∨ valuation q 1435 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1439)) (countLit q [-48]) (countLit q [-49]) (count1439 q) 1 (meaningNeg49 q) (meaning1439 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1439 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1439)) (countLit q [-48]) (countLit q [-49]) (count1439 q) 1 (meaningNeg48 q) (meaning1439 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1439 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 49 = true ∨ valuationOf q 1440 = true := by
  have hs : count1439 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (1440)) (countLit q [-48]) (countLit q [-49]) (count1439 q) 1 1 (meaningNeg48 q) (meaningNeg49 q) (meaning1440 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 1440 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-44]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-48, -49])
  have hm := merge_right (literal (valuationOf q) (1439)) (literal (valuationOf q) (1441)) (countLit q [-44]) (countLit q [-48, -49]) (count1441 q) 1 (meaning1439 q) (meaning1441 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1441 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-44]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-48, -49])
  have hm := merge_right (literal (valuationOf q) (1440)) (literal (valuationOf q) (1442)) (countLit q [-44]) (countLit q [-48, -49]) (count1441 q) 2 (meaning1440 q) (meaning1442 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1442 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-44]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-48, -49])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1441)) (countLit q [-44]) (countLit q [-48, -49]) (count1441 q) 1 (meaningNeg44 q) (meaning1441 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1441 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1439 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-44]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-48, -49])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1442)) (countLit q [-44]) (countLit q [-48, -49]) (count1441 q) 1 1 (meaningNeg44 q) (meaning1439 q) (meaning1442 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1439 = false ∨ valuation q 1442 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1440 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-44]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-48, -49])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1443)) (countLit q [-44]) (countLit q [-48, -49]) (count1441 q) 1 2 (meaningNeg44 q) (meaning1440 q) (meaning1443 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1440 = false ∨ valuation q 1443 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1444 = true := by
  have hs : count1444 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1444)) (countLit q [-52]) (countLit q [-54]) (count1444 q) 1 (meaningNeg54 q) (meaning1444 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1444 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E171.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112171
