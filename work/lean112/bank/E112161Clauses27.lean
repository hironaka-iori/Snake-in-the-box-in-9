import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1388 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1377)) (literal (valuationOf q) (1388)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 3 (meaning1377 q) (meaning1388 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1388 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1389 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1377)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1389)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 3 1 (meaning1377 q) (meaning1382 q) (meaning1389 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1382 = false ∨ valuation q 1389 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1390 = true := by
  have hs : count1386 q = (countLit q [-30, -32, -33]) + (countLit q [-35, -39, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33]) (l₂ := [-35, -39, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1377)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1390)) (countLit q [-30, -32, -33]) (countLit q [-35, -39, -40, -42]) (count1386 q) 3 2 (meaning1377 q) (meaning1383 q) (meaning1390 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1383 = false ∨ valuation q 1390 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1393 = true := by
  have hs : count1393 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1393)) (countLit q [-46]) (countLit q [-47]) (count1393 q) 1 (meaningNeg47 q) (meaning1393 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1393 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1393 = true := by
  have hs : count1393 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1393)) (countLit q [-46]) (countLit q [-47]) (count1393 q) 1 (meaningNeg46 q) (meaning1393 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1393 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 47 = true ∨ valuationOf q 1394 = true := by
  have hs : count1393 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (1394)) (countLit q [-46]) (countLit q [-47]) (count1393 q) 1 1 (meaningNeg46 q) (meaningNeg47 q) (meaning1394 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 1394 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-45]) + (countLit q [-46, -47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46, -47])
  have hm := merge_right (literal (valuationOf q) (1393)) (literal (valuationOf q) (1395)) (countLit q [-45]) (countLit q [-46, -47]) (count1395 q) 1 (meaning1393 q) (meaning1395 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1395 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1396 = true := by
  have hs : count1395 q = (countLit q [-45]) + (countLit q [-46, -47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46, -47])
  have hm := merge_right (literal (valuationOf q) (1394)) (literal (valuationOf q) (1396)) (countLit q [-45]) (countLit q [-46, -47]) (count1395 q) 2 (meaning1394 q) (meaning1396 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1396 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-45]) + (countLit q [-46, -47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46, -47])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1395)) (countLit q [-45]) (countLit q [-46, -47]) (count1395 q) 1 (meaningNeg45 q) (meaning1395 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1395 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1393 = false ∨ valuationOf q 1396 = true := by
  have hs : count1395 q = (countLit q [-45]) + (countLit q [-46, -47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46, -47])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1396)) (countLit q [-45]) (countLit q [-46, -47]) (count1395 q) 1 1 (meaningNeg45 q) (meaning1393 q) (meaning1396 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1393 = false ∨ valuation q 1396 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1394 = false ∨ valuationOf q 1397 = true := by
  have hs : count1395 q = (countLit q [-45]) + (countLit q [-46, -47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46, -47])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1397)) (countLit q [-45]) (countLit q [-46, -47]) (count1395 q) 1 2 (meaningNeg45 q) (meaning1394 q) (meaning1397 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1394 = false ∨ valuation q 1397 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1398)) (countLit q [-50]) (countLit q [-51]) (count1398 q) 1 (meaningNeg51 q) (meaning1398 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1398 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1398)) (countLit q [-50]) (countLit q [-51]) (count1398 q) 1 (meaningNeg50 q) (meaning1398 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1398 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1399 = true := by
  have hs : count1398 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1399)) (countLit q [-50]) (countLit q [-51]) (count1398 q) 1 1 (meaningNeg50 q) (meaningNeg51 q) (meaning1399 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 1399 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1400 = true := by
  have hs : count1400 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1400)) (countLit q [-53]) (countLit q [-54]) (count1400 q) 1 (meaningNeg54 q) (meaning1400 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1400 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1400 = true := by
  have hs : count1400 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1400)) (countLit q [-53]) (countLit q [-54]) (count1400 q) 1 (meaningNeg53 q) (meaning1400 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1400 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1401 = true := by
  have hs : count1400 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1401)) (countLit q [-53]) (countLit q [-54]) (count1400 q) 1 1 (meaningNeg53 q) (meaningNeg54 q) (meaning1401 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 54 = true ∨ valuation q 1401 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-50, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-53, -54])
  have hm := merge_right (literal (valuationOf q) (1400)) (literal (valuationOf q) (1402)) (countLit q [-50, -51]) (countLit q [-53, -54]) (count1402 q) 1 (meaning1400 q) (meaning1402 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1402 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-50, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-53, -54])
  have hm := merge_right (literal (valuationOf q) (1401)) (literal (valuationOf q) (1403)) (countLit q [-50, -51]) (countLit q [-53, -54]) (count1402 q) 2 (meaning1401 q) (meaning1403 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1403 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-50, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-53, -54])
  have hm := merge_left (literal (valuationOf q) (1398)) (literal (valuationOf q) (1402)) (countLit q [-50, -51]) (countLit q [-53, -54]) (count1402 q) 1 (meaning1398 q) (meaning1402 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1402 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-50, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1398)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1403)) (countLit q [-50, -51]) (countLit q [-53, -54]) (count1402 q) 1 1 (meaning1398 q) (meaning1400 q) (meaning1403 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1400 = false ∨ valuation q 1403 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1404 = true := by
  have hs : count1402 q = (countLit q [-50, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1398)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1404)) (countLit q [-50, -51]) (countLit q [-53, -54]) (count1402 q) 1 2 (meaning1398 q) (meaning1401 q) (meaning1404 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1401 = false ∨ valuation q 1404 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-50, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-53, -54])
  have hm := merge_left (literal (valuationOf q) (1399)) (literal (valuationOf q) (1403)) (countLit q [-50, -51]) (countLit q [-53, -54]) (count1402 q) 2 (meaning1399 q) (meaning1403 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1403 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1404 = true := by
  have hs : count1402 q = (countLit q [-50, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1404)) (countLit q [-50, -51]) (countLit q [-53, -54]) (count1402 q) 2 1 (meaning1399 q) (meaning1400 q) (meaning1404 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1400 = false ∨ valuation q 1404 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1405 = true := by
  have hs : count1402 q = (countLit q [-50, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1405)) (countLit q [-50, -51]) (countLit q [-53, -54]) (count1402 q) 2 2 (meaning1399 q) (meaning1401 q) (meaning1405 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1401 = false ∨ valuation q 1405 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_right (literal (valuationOf q) (1402)) (literal (valuationOf q) (1406)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 1 (meaning1402 q) (meaning1406 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1406 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_right (literal (valuationOf q) (1403)) (literal (valuationOf q) (1407)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 2 (meaning1403 q) (meaning1407 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1407 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1408 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_right (literal (valuationOf q) (1404)) (literal (valuationOf q) (1408)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 3 (meaning1404 q) (meaning1408 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1408 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1409 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_right (literal (valuationOf q) (1405)) (literal (valuationOf q) (1409)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 4 (meaning1405 q) (meaning1409 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1409 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_left (literal (valuationOf q) (1395)) (literal (valuationOf q) (1406)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 1 (meaning1395 q) (meaning1406 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1406 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1407)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 1 1 (meaning1395 q) (meaning1402 q) (meaning1407 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1402 = false ∨ valuation q 1407 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1408 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1408)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 1 2 (meaning1395 q) (meaning1403 q) (meaning1408 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1403 = false ∨ valuation q 1408 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E161.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112161
