import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1367 = true := by
  have hs : count1367 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1367)) (countLit q [-2]) (countLit q [-4, -5]) (count1367 q) 1 (meaningNeg2 q) (meaning1367 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1367 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1365 = false ∨ valuationOf q 1368 = true := by
  have hs : count1367 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1365)) (literal (valuationOf q) (1368)) (countLit q [-2]) (countLit q [-4, -5]) (count1367 q) 1 1 (meaningNeg2 q) (meaning1365 q) (meaning1368 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1365 = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1365 = false ∨ valuation q 1368 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1366 = false ∨ valuationOf q 1369 = true := by
  have hs : count1367 q = (countLit q [-2]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1366)) (literal (valuationOf q) (1369)) (countLit q [-2]) (countLit q [-4, -5]) (count1367 q) 1 2 (meaningNeg2 q) (meaning1366 q) (meaning1369 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1366 = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1366 = false ∨ valuation q 1369 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (1370)) (countLit q [-8]) (countLit q [-9]) (count1370 q) 1 (meaningNeg9 q) (meaning1370 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1370 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1372 = true := by
  have hs : count1372 q = (countLit q [-11]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14])
  have hm := merge_right (literal (valuationOf q) (-14)) (literal (valuationOf q) (1372)) (countLit q [-11]) (countLit q [-14]) (count1372 q) 1 (meaningNeg14 q) (meaning1372 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1372 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1372 = true := by
  have hs : count1372 q = (countLit q [-11]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1372)) (countLit q [-11]) (countLit q [-14]) (count1372 q) 1 (meaningNeg11 q) (meaning1372 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1372 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1372 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 14 = true ∨ valuationOf q 1373 = true := by
  have hs : count1372 q = (countLit q [-11]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-14)) (literal (valuationOf q) (1373)) (countLit q [-11]) (countLit q [-14]) (count1372 q) 1 1 (meaningNeg11 q) (meaningNeg14 q) (meaning1373 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 14)) = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 1373 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1374 = true := by
  have hs : count1374 q = (countLit q [-8, -9]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-11, -14])
  have hm := merge_right (literal (valuationOf q) (1372)) (literal (valuationOf q) (1374)) (countLit q [-8, -9]) (countLit q [-11, -14]) (count1374 q) 1 (meaning1372 q) (meaning1374 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1374 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1375 = true := by
  have hs : count1374 q = (countLit q [-8, -9]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-11, -14])
  have hm := merge_right (literal (valuationOf q) (1373)) (literal (valuationOf q) (1375)) (countLit q [-8, -9]) (countLit q [-11, -14]) (count1374 q) 2 (meaning1373 q) (meaning1375 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1375 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1374 = true := by
  have hs : count1374 q = (countLit q [-8, -9]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-11, -14])
  have hm := merge_left (literal (valuationOf q) (1370)) (literal (valuationOf q) (1374)) (countLit q [-8, -9]) (countLit q [-11, -14]) (count1374 q) 1 (meaning1370 q) (meaning1374 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1374 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1375 = true := by
  have hs : count1374 q = (countLit q [-8, -9]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-11, -14])
  have hm := merge_two (literal (valuationOf q) (1370)) (literal (valuationOf q) (1372)) (literal (valuationOf q) (1375)) (countLit q [-8, -9]) (countLit q [-11, -14]) (count1374 q) 1 1 (meaning1370 q) (meaning1372 q) (meaning1375 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1372 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1372 = false ∨ valuation q 1375 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 1370 = false ∨ valuationOf q 1373 = false ∨ valuationOf q 1376 = true := by
  have hs : count1374 q = (countLit q [-8, -9]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-11, -14])
  have hm := merge_two (literal (valuationOf q) (1370)) (literal (valuationOf q) (1373)) (literal (valuationOf q) (1376)) (countLit q [-8, -9]) (countLit q [-11, -14]) (count1374 q) 1 2 (meaning1370 q) (meaning1373 q) (meaning1376 q) hs
  change valuationOf q 1370 = false ∨ valuationOf q 1373 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 1370 = false ∨ valuation q 1373 = false ∨ valuation q 1376 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1378 = true := by
  have hs : count1378 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -11, -14])
  have hm := merge_right (literal (valuationOf q) (1374)) (literal (valuationOf q) (1378)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -11, -14]) (count1378 q) 1 (meaning1374 q) (meaning1378 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1378 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1379 = true := by
  have hs : count1378 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -11, -14])
  have hm := merge_right (literal (valuationOf q) (1375)) (literal (valuationOf q) (1379)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -11, -14]) (count1378 q) 2 (meaning1375 q) (meaning1379 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1379 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1378 = true := by
  have hs : count1378 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -11, -14])
  have hm := merge_left (literal (valuationOf q) (1367)) (literal (valuationOf q) (1378)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -11, -14]) (count1378 q) 1 (meaning1367 q) (meaning1378 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1378 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1379 = true := by
  have hs : count1378 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -11, -14])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1379)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -11, -14]) (count1378 q) 1 1 (meaning1367 q) (meaning1374 q) (meaning1379 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1374 = false ∨ valuation q 1379 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1380 = true := by
  have hs : count1378 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -11, -14])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1380)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -11, -14]) (count1378 q) 1 2 (meaning1367 q) (meaning1375 q) (meaning1380 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1375 = false ∨ valuation q 1380 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 1367 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1381 = true := by
  have hs : count1378 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -11, -14])
  have hm := merge_two (literal (valuationOf q) (1367)) (literal (valuationOf q) (1376)) (literal (valuationOf q) (1381)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -11, -14]) (count1378 q) 1 3 (meaning1367 q) (meaning1376 q) (meaning1381 q) hs
  change valuationOf q 1367 = false ∨ valuationOf q 1376 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 1367 = false ∨ valuation q 1376 = false ∨ valuation q 1381 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1379 = true := by
  have hs : count1378 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -11, -14])
  have hm := merge_left (literal (valuationOf q) (1368)) (literal (valuationOf q) (1379)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -11, -14]) (count1378 q) 2 (meaning1368 q) (meaning1379 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1379 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1380 = true := by
  have hs : count1378 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -11, -14])
  have hm := merge_two (literal (valuationOf q) (1368)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1380)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -11, -14]) (count1378 q) 2 1 (meaning1368 q) (meaning1374 q) (meaning1380 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1374 = false ∨ valuation q 1380 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1381 = true := by
  have hs : count1378 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -11, -14])
  have hm := merge_two (literal (valuationOf q) (1368)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1381)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -11, -14]) (count1378 q) 2 2 (meaning1368 q) (meaning1375 q) (meaning1381 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1375 = false ∨ valuation q 1381 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1381 = true := by
  have hs : count1378 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -11, -14])
  have hm := merge_two (literal (valuationOf q) (1369)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1381)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -11, -14]) (count1378 q) 3 1 (meaning1369 q) (meaning1374 q) (meaning1381 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1374 = false ∨ valuation q 1381 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1382 = true := by
  have hs : count1378 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -11, -14])
  have hm := merge_two (literal (valuationOf q) (1369)) (literal (valuationOf q) (1375)) (literal (valuationOf q) (1382)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -11, -14]) (count1378 q) 3 2 (meaning1369 q) (meaning1375 q) (meaning1382 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1375 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1375 = false ∨ valuation q 1382 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1385 = true := by
  have hs : count1385 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1385)) (countLit q [-18]) (countLit q [-19]) (count1385 q) 1 (meaningNeg19 q) (meaning1385 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1385 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1385 = true := by
  have hs : count1385 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1385)) (countLit q [-18]) (countLit q [-19]) (count1385 q) 1 (meaningNeg18 q) (meaning1385 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1385 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 19 = true ∨ valuationOf q 1386 = true := by
  have hs : count1385 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (1386)) (countLit q [-18]) (countLit q [-19]) (count1385 q) 1 1 (meaningNeg18 q) (meaningNeg19 q) (meaning1386 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 1386 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1387 = true := by
  have hs : count1387 q = (countLit q [-17]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -19])
  have hm := merge_right (literal (valuationOf q) (1385)) (literal (valuationOf q) (1387)) (countLit q [-17]) (countLit q [-18, -19]) (count1387 q) 1 (meaning1385 q) (meaning1387 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1387 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1388 = true := by
  have hs : count1387 q = (countLit q [-17]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -19])
  have hm := merge_right (literal (valuationOf q) (1386)) (literal (valuationOf q) (1388)) (countLit q [-17]) (countLit q [-18, -19]) (count1387 q) 2 (meaning1386 q) (meaning1388 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1388 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1387 = true := by
  have hs : count1387 q = (countLit q [-17]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -19])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1387)) (countLit q [-17]) (countLit q [-18, -19]) (count1387 q) 1 (meaningNeg17 q) (meaning1387 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1387 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1385 = false ∨ valuationOf q 1388 = true := by
  have hs : count1387 q = (countLit q [-17]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1388)) (countLit q [-17]) (countLit q [-18, -19]) (count1387 q) 1 1 (meaningNeg17 q) (meaning1385 q) (meaning1388 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1385 = false ∨ valuation q 1388 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1390 = true := by
  have hs : count1390 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1390)) (countLit q [-21]) (countLit q [-23]) (count1390 q) 1 (meaningNeg23 q) (meaning1390 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1390 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1390 = true := by
  have hs : count1390 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1390)) (countLit q [-21]) (countLit q [-23]) (count1390 q) 1 (meaningNeg21 q) (meaning1390 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1390 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E171.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112171
