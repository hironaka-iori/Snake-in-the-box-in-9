import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1425 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1413)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1425)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 1 1 (meaning1413 q) (meaning1420 q) (meaning1425 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1420 = false ∨ valuation q 1425 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1426 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1413)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1426)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 1 2 (meaning1413 q) (meaning1421 q) (meaning1426 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1421 = false ∨ valuation q 1426 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1413)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1427)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 1 3 (meaning1413 q) (meaning1422 q) (meaning1427 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1422 = false ∨ valuation q 1427 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1428 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1413)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1428)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 1 4 (meaning1413 q) (meaning1423 q) (meaning1428 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1423 = false ∨ valuation q 1428 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1425 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_left (literal (valuationOf q) (1414)) (literal (valuationOf q) (1425)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 2 (meaning1414 q) (meaning1425 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1425 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1426 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1426)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 2 1 (meaning1414 q) (meaning1420 q) (meaning1426 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1420 = false ∨ valuation q 1426 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1427 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1427)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 2 2 (meaning1414 q) (meaning1421 q) (meaning1427 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1421 = false ∨ valuation q 1427 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1428 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1428)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 2 3 (meaning1414 q) (meaning1422 q) (meaning1428 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1422 = false ∨ valuation q 1428 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1426 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_left (literal (valuationOf q) (1415)) (literal (valuationOf q) (1426)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 3 (meaning1415 q) (meaning1426 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1426 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1427 = true := by
  have hs : count1424 q = (countLit q [-2, -4, -5]) + (countLit q [-6, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-6, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1427)) (countLit q [-2, -4, -5]) (countLit q [-6, -10, -11, -12]) (count1424 q) 3 1 (meaning1415 q) (meaning1420 q) (meaning1427 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1420 = false ∨ valuation q 1427 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1431 = true := by
  have hs : count1431 q = (countLit q [-18]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1431)) (countLit q [-18]) (countLit q [-21]) (count1431 q) 1 (meaningNeg21 q) (meaning1431 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1431 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1431 = true := by
  have hs : count1431 q = (countLit q [-18]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1431)) (countLit q [-18]) (countLit q [-21]) (count1431 q) 1 (meaningNeg18 q) (meaning1431 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1431 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 21 = true ∨ valuationOf q 1432 = true := by
  have hs : count1431 q = (countLit q [-18]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (1432)) (countLit q [-18]) (countLit q [-21]) (count1431 q) 1 1 (meaningNeg18 q) (meaningNeg21 q) (meaning1432 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 21 = true ∨ valuation q 1432 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-15]) + (countLit q [-18, -21]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18, -21])
  have hm := merge_right (literal (valuationOf q) (1431)) (literal (valuationOf q) (1433)) (countLit q [-15]) (countLit q [-18, -21]) (count1433 q) 1 (meaning1431 q) (meaning1433 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1433 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-15]) + (countLit q [-18, -21]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18, -21])
  have hm := merge_right (literal (valuationOf q) (1432)) (literal (valuationOf q) (1434)) (countLit q [-15]) (countLit q [-18, -21]) (count1433 q) 2 (meaning1432 q) (meaning1434 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1434 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-15]) + (countLit q [-18, -21]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18, -21])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1433)) (countLit q [-15]) (countLit q [-18, -21]) (count1433 q) 1 (meaningNeg15 q) (meaning1433 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1433 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1431 = false ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-15]) + (countLit q [-18, -21]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18, -21])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1434)) (countLit q [-15]) (countLit q [-18, -21]) (count1433 q) 1 1 (meaningNeg15 q) (meaning1431 q) (meaning1434 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1431 = false ∨ valuation q 1434 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1432 = false ∨ valuationOf q 1435 = true := by
  have hs : count1433 q = (countLit q [-15]) + (countLit q [-18, -21]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18, -21])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1435)) (countLit q [-15]) (countLit q [-18, -21]) (count1433 q) 1 2 (meaningNeg15 q) (meaning1432 q) (meaning1435 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1432 = false ∨ valuation q 1435 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1436 = true := by
  have hs : count1436 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1436)) (countLit q [-22]) (countLit q [-23]) (count1436 q) 1 (meaningNeg23 q) (meaning1436 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1436 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1436 = true := by
  have hs : count1436 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1436)) (countLit q [-22]) (countLit q [-23]) (count1436 q) 1 (meaningNeg22 q) (meaning1436 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1436 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 23 = true ∨ valuationOf q 1437 = true := by
  have hs : count1436 q = (countLit q [-22]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (1437)) (countLit q [-22]) (countLit q [-23]) (count1436 q) 1 1 (meaningNeg22 q) (meaningNeg23 q) (meaning1437 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 23 = true ∨ valuation q 1437 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_right (literal (valuationOf q) (-27)) (literal (valuationOf q) (1438)) (countLit q [-25]) (countLit q [-27]) (count1438 q) 1 (meaningNeg27 q) (meaning1438 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1438 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1438)) (countLit q [-25]) (countLit q [-27]) (count1438 q) 1 (meaningNeg25 q) (meaning1438 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1438 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 27 = true ∨ valuationOf q 1439 = true := by
  have hs : count1438 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-27)) (literal (valuationOf q) (1439)) (countLit q [-25]) (countLit q [-27]) (count1438 q) 1 1 (meaningNeg25 q) (meaningNeg27 q) (meaning1439 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 27)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 1439 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1440 = true := by
  have hs : count1440 q = (countLit q [-22, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-25, -27])
  have hm := merge_right (literal (valuationOf q) (1438)) (literal (valuationOf q) (1440)) (countLit q [-22, -23]) (countLit q [-25, -27]) (count1440 q) 1 (meaning1438 q) (meaning1440 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1440 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1440 = true := by
  have hs : count1440 q = (countLit q [-22, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-25, -27])
  have hm := merge_left (literal (valuationOf q) (1436)) (literal (valuationOf q) (1440)) (countLit q [-22, -23]) (countLit q [-25, -27]) (count1440 q) 1 (meaning1436 q) (meaning1440 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1440 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1441 = true := by
  have hs : count1440 q = (countLit q [-22, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1441)) (countLit q [-22, -23]) (countLit q [-25, -27]) (count1440 q) 1 1 (meaning1436 q) (meaning1438 q) (meaning1441 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1438 = false ∨ valuation q 1441 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1442 = true := by
  have hs : count1440 q = (countLit q [-22, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1442)) (countLit q [-22, -23]) (countLit q [-25, -27]) (count1440 q) 1 2 (meaning1436 q) (meaning1439 q) (meaning1442 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1439 = false ∨ valuation q 1442 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1441 = true := by
  have hs : count1440 q = (countLit q [-22, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-25, -27])
  have hm := merge_left (literal (valuationOf q) (1437)) (literal (valuationOf q) (1441)) (countLit q [-22, -23]) (countLit q [-25, -27]) (count1440 q) 2 (meaning1437 q) (meaning1441 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1441 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1442 = true := by
  have hs : count1440 q = (countLit q [-22, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1438)) (literal (valuationOf q) (1442)) (countLit q [-22, -23]) (countLit q [-25, -27]) (count1440 q) 2 1 (meaning1437 q) (meaning1438 q) (meaning1442 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1438 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1438 = false ∨ valuation q 1442 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1443 = true := by
  have hs : count1440 q = (countLit q [-22, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-22, -23]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1443)) (countLit q [-22, -23]) (countLit q [-25, -27]) (count1440 q) 2 2 (meaning1437 q) (meaning1439 q) (meaning1443 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1439 = false ∨ valuation q 1443 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1444 = true := by
  have hs : count1444 q = (countLit q [-15, -18, -21]) + (countLit q [-22, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -21]) (l₂ := [-22, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (1440)) (literal (valuationOf q) (1444)) (countLit q [-15, -18, -21]) (countLit q [-22, -23, -25, -27]) (count1444 q) 1 (meaning1440 q) (meaning1444 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1444 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E207.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112207
