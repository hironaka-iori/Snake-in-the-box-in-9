import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1366 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1355)) (literal (valuationOf q) (1366)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 4 4 (meaning1335 q) (meaning1355 q) (meaning1366 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1355 = false ∨ valuation q 1366 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1367 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1367)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 4 5 (meaning1335 q) (meaning1356 q) (meaning1367 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1356 = false ∨ valuation q 1367 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (1373)) (countLit q [-32]) (countLit q [-33]) (count1373 q) 1 (meaningNeg33 q) (meaning1373 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1373 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1373)) (countLit q [-32]) (countLit q [-33]) (count1373 q) 1 (meaningNeg32 q) (meaning1373 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1373 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 33 = true ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (1374)) (countLit q [-32]) (countLit q [-33]) (count1373 q) 1 1 (meaningNeg32 q) (meaningNeg33 q) (meaning1374 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 33 = true ∨ valuation q 1374 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1375 = true := by
  have hs : count1375 q = (countLit q [-30]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -33])
  have hm := merge_right (literal (valuationOf q) (1373)) (literal (valuationOf q) (1375)) (countLit q [-30]) (countLit q [-32, -33]) (count1375 q) 1 (meaning1373 q) (meaning1375 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1375 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1376 = true := by
  have hs : count1375 q = (countLit q [-30]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -33])
  have hm := merge_right (literal (valuationOf q) (1374)) (literal (valuationOf q) (1376)) (countLit q [-30]) (countLit q [-32, -33]) (count1375 q) 2 (meaning1374 q) (meaning1376 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1376 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1375 = true := by
  have hs : count1375 q = (countLit q [-30]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -33])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1375)) (countLit q [-30]) (countLit q [-32, -33]) (count1375 q) 1 (meaningNeg30 q) (meaning1375 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1375 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1373 = false ∨ valuationOf q 1376 = true := by
  have hs : count1375 q = (countLit q [-30]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -33])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1373)) (literal (valuationOf q) (1376)) (countLit q [-30]) (countLit q [-32, -33]) (count1375 q) 1 1 (meaningNeg30 q) (meaning1373 q) (meaning1376 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1373 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1373 = false ∨ valuation q 1376 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1374 = false ∨ valuationOf q 1377 = true := by
  have hs : count1375 q = (countLit q [-30]) + (countLit q [-32, -33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -33])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1377)) (countLit q [-30]) (countLit q [-32, -33]) (count1375 q) 1 2 (meaningNeg30 q) (meaning1374 q) (meaning1377 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1374 = false ∨ valuation q 1377 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1378 = true := by
  have hs : count1378 q = (countLit q [-35]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (1378)) (countLit q [-35]) (countLit q [-39]) (count1378 q) 1 (meaningNeg39 q) (meaning1378 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1378 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1378 = true := by
  have hs : count1378 q = (countLit q [-35]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1378)) (countLit q [-35]) (countLit q [-39]) (count1378 q) 1 (meaningNeg35 q) (meaning1378 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1378 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 39 = true ∨ valuationOf q 1379 = true := by
  have hs : count1378 q = (countLit q [-35]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-39])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-39)) (literal (valuationOf q) (1379)) (countLit q [-35]) (countLit q [-39]) (count1378 q) 1 1 (meaningNeg35 q) (meaningNeg39 q) (meaning1379 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 39)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 39 = true ∨ valuation q 1379 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1380 = true := by
  have hs : count1380 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1380)) (countLit q [-40]) (countLit q [-42]) (count1380 q) 1 (meaningNeg42 q) (meaning1380 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1380 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1380 = true := by
  have hs : count1380 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1380)) (countLit q [-40]) (countLit q [-42]) (count1380 q) 1 (meaningNeg40 q) (meaning1380 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1380 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1381 = true := by
  have hs : count1380 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1381)) (countLit q [-40]) (countLit q [-42]) (count1380 q) 1 1 (meaningNeg40 q) (meaningNeg42 q) (meaning1381 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 1381 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1382 = true := by
  have hs : count1382 q = (countLit q [-35, -39]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -39]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1380)) (literal (valuationOf q) (1382)) (countLit q [-35, -39]) (countLit q [-40, -42]) (count1382 q) 1 (meaning1380 q) (meaning1382 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1382 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1383 = true := by
  have hs : count1382 q = (countLit q [-35, -39]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -39]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1381)) (literal (valuationOf q) (1383)) (countLit q [-35, -39]) (countLit q [-40, -42]) (count1382 q) 2 (meaning1381 q) (meaning1383 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1383 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1382 = true := by
  have hs : count1382 q = (countLit q [-35, -39]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -39]) (l₂ := [-40, -42])
  have hm := merge_left (literal (valuationOf q) (1378)) (literal (valuationOf q) (1382)) (countLit q [-35, -39]) (countLit q [-40, -42]) (count1382 q) 1 (meaning1378 q) (meaning1382 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1382 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1383 = true := by
  have hs : count1382 q = (countLit q [-35, -39]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -39]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1383)) (countLit q [-35, -39]) (countLit q [-40, -42]) (count1382 q) 1 1 (meaning1378 q) (meaning1380 q) (meaning1383 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1380 = false ∨ valuation q 1383 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true := by
  have hs : count1382 q = (countLit q [-35, -39]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -39]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1384)) (countLit q [-35, -39]) (countLit q [-40, -42]) (count1382 q) 1 2 (meaning1378 q) (meaning1381 q) (meaning1384 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1381 = false ∨ valuation q 1384 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1384 = true := by
  have hs : count1382 q = (countLit q [-35, -39]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-35, -39]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1379)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1384)) (countLit q [-35, -39]) (countLit q [-40, -42]) (count1382 q) 2 1 (meaning1379 q) (meaning1380 q) (meaning1384 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1380 = false ∨ valuation q 1384 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1382)) (literal (valuationOf q) (1386)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 1 (meaning1382 q) (meaning1386 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1386 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1383)) (literal (valuationOf q) (1387)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 2 (meaning1383 q) (meaning1387 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1387 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1388 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1384)) (literal (valuationOf q) (1388)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 3 (meaning1384 q) (meaning1388 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1388 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1375)) (literal (valuationOf q) (1386)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 1 (meaning1375 q) (meaning1386 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1386 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1387)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 1 1 (meaning1375 q) (meaning1382 q) (meaning1387 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1382 = false ∨ valuation q 1387 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1388 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1388)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 1 2 (meaning1375 q) (meaning1383 q) (meaning1388 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1383 = false ∨ valuation q 1388 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1376)) (literal (valuationOf q) (1387)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 2 (meaning1376 q) (meaning1387 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1387 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1388 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1388)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 2 1 (meaning1376 q) (meaning1382 q) (meaning1388 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1382 = false ∨ valuation q 1388 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1389 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1389)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 2 2 (meaning1376 q) (meaning1383 q) (meaning1389 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1383 = false ∨ valuation q 1389 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1390 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1390)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 2 3 (meaning1376 q) (meaning1384 q) (meaning1390 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1384 = false ∨ valuation q 1390 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E161.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112161
