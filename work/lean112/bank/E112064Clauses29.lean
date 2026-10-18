import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1415 = true := by
  have hs : count1412 q = (countLit q [-6, -12]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-6, -12]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (1409)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1415)) (countLit q [-6, -12]) (countLit q [-13, -15]) (count1412 q) 2 2 (meaning1409 q) (meaning1411 q) (meaning1415 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1411 = false ∨ valuation q 1415 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1416 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1412)) (literal (valuationOf q) (1416)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 1 (meaning1412 q) (meaning1416 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1416 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1417 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1413)) (literal (valuationOf q) (1417)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 2 (meaning1413 q) (meaning1417 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1417 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1418 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1414)) (literal (valuationOf q) (1418)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 3 (meaning1414 q) (meaning1418 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1418 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1419 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1415)) (literal (valuationOf q) (1419)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 4 (meaning1415 q) (meaning1419 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1419 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1416 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_left (literal (valuationOf q) (1405)) (literal (valuationOf q) (1416)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 1 (meaning1405 q) (meaning1416 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1416 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1417 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1417)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 1 1 (meaning1405 q) (meaning1412 q) (meaning1417 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1412 = false ∨ valuation q 1417 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1418 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1418)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 1 2 (meaning1405 q) (meaning1413 q) (meaning1418 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1413 = false ∨ valuation q 1418 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1419 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1414)) (literal (valuationOf q) (1419)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 1 3 (meaning1405 q) (meaning1414 q) (meaning1419 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1414 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1414 = false ∨ valuation q 1419 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1417 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_left (literal (valuationOf q) (1406)) (literal (valuationOf q) (1417)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 2 (meaning1406 q) (meaning1417 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1417 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1418 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1418)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 2 1 (meaning1406 q) (meaning1412 q) (meaning1418 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1412 = false ∨ valuation q 1418 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1419 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1419)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 2 2 (meaning1406 q) (meaning1413 q) (meaning1419 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1413 = false ∨ valuation q 1419 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1418 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_left (literal (valuationOf q) (1407)) (literal (valuationOf q) (1418)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 3 (meaning1407 q) (meaning1418 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1418 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1419 = true := by
  have hs : count1416 q = (countLit q [-2, -3, -5]) + (countLit q [-6, -12, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-6, -12, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1419)) (countLit q [-2, -3, -5]) (countLit q [-6, -12, -13, -15]) (count1416 q) 3 1 (meaning1407 q) (meaning1412 q) (meaning1419 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1412 = false ∨ valuation q 1419 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1423)) (countLit q [-19]) (countLit q [-20]) (count1423 q) 1 (meaningNeg20 q) (meaning1423 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1423 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1423)) (countLit q [-19]) (countLit q [-20]) (count1423 q) 1 (meaningNeg19 q) (meaning1423 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1423 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 20 = true ∨ valuationOf q 1424 = true := by
  have hs : count1423 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (1424)) (countLit q [-19]) (countLit q [-20]) (count1423 q) 1 1 (meaningNeg19 q) (meaningNeg20 q) (meaning1424 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 20 = true ∨ valuation q 1424 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-16]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19, -20])
  have hm := merge_right (literal (valuationOf q) (1423)) (literal (valuationOf q) (1425)) (countLit q [-16]) (countLit q [-19, -20]) (count1425 q) 1 (meaning1423 q) (meaning1425 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1425 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-16]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19, -20])
  have hm := merge_right (literal (valuationOf q) (1424)) (literal (valuationOf q) (1426)) (countLit q [-16]) (countLit q [-19, -20]) (count1425 q) 2 (meaning1424 q) (meaning1426 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1426 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-16]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19, -20])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1425)) (countLit q [-16]) (countLit q [-19, -20]) (count1425 q) 1 (meaningNeg16 q) (meaning1425 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1425 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1423 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-16]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19, -20])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1426)) (countLit q [-16]) (countLit q [-19, -20]) (count1425 q) 1 1 (meaningNeg16 q) (meaning1423 q) (meaning1426 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1423 = false ∨ valuation q 1426 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1424 = false ∨ valuationOf q 1427 = true := by
  have hs : count1425 q = (countLit q [-16]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19, -20])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (1424)) (literal (valuationOf q) (1427)) (countLit q [-16]) (countLit q [-19, -20]) (count1425 q) 1 2 (meaningNeg16 q) (meaning1424 q) (meaning1427 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1424 = false ∨ valuation q 1427 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1428)) (countLit q [-22]) (countLit q [-24]) (count1428 q) 1 (meaningNeg24 q) (meaning1428 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1428 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1429 = true := by
  have hs : count1428 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1429)) (countLit q [-22]) (countLit q [-24]) (count1428 q) 1 1 (meaningNeg22 q) (meaningNeg24 q) (meaning1429 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 24 = true ∨ valuation q 1429 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1430 = true := by
  have hs : count1430 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1430)) (countLit q [-25]) (countLit q [-26]) (count1430 q) 1 (meaningNeg26 q) (meaning1430 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1430 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 26 = true ∨ valuationOf q 1431 = true := by
  have hs : count1430 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (1431)) (countLit q [-25]) (countLit q [-26]) (count1430 q) 1 1 (meaningNeg25 q) (meaningNeg26 q) (meaning1431 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 26 = true ∨ valuation q 1431 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1433 = true := by
  have hs : count1432 q = (countLit q [-22, -24]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1433)) (countLit q [-22, -24]) (countLit q [-25, -26]) (count1432 q) 1 1 (meaning1428 q) (meaning1430 q) (meaning1433 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1430 = false ∨ valuation q 1433 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1434 = true := by
  have hs : count1432 q = (countLit q [-22, -24]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1434)) (countLit q [-22, -24]) (countLit q [-25, -26]) (count1432 q) 1 2 (meaning1428 q) (meaning1431 q) (meaning1434 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1431 = false ∨ valuation q 1434 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1434 = true := by
  have hs : count1432 q = (countLit q [-22, -24]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1434)) (countLit q [-22, -24]) (countLit q [-25, -26]) (count1432 q) 2 1 (meaning1429 q) (meaning1430 q) (meaning1434 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1430 = false ∨ valuation q 1434 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1435 = true := by
  have hs : count1432 q = (countLit q [-22, -24]) + (countLit q [-25, -26]) := List.countP_append (p := literal q) (l₁ := [-22, -24]) (l₂ := [-25, -26])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1435)) (countLit q [-22, -24]) (countLit q [-25, -26]) (count1432 q) 2 2 (meaning1429 q) (meaning1431 q) (meaning1435 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1431 = false ∨ valuation q 1435 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1437 = true := by
  have hs : count1436 q = (countLit q [-16, -19, -20]) + (countLit q [-22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -20]) (l₂ := [-22, -24, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1433)) (literal (valuationOf q) (1437)) (countLit q [-16, -19, -20]) (countLit q [-22, -24, -25, -26]) (count1436 q) 2 (meaning1433 q) (meaning1437 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1437 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1438 = true := by
  have hs : count1436 q = (countLit q [-16, -19, -20]) + (countLit q [-22, -24, -25, -26]) := List.countP_append (p := literal q) (l₁ := [-16, -19, -20]) (l₂ := [-22, -24, -25, -26])
  have hm := merge_right (literal (valuationOf q) (1434)) (literal (valuationOf q) (1438)) (countLit q [-16, -19, -20]) (countLit q [-22, -24, -25, -26]) (count1436 q) 3 (meaning1434 q) (meaning1438 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1438 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E064.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112064
